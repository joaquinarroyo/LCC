/// Routines to manage the overall operation of the file system.  Implements
/// routines to map from textual file names to files.
///
/// Each file in the file system has:
/// * a file header, stored in a sector on disk (the size of the file header
///   data structure is arranged to be precisely the size of 1 disk sector);
/// * a number of data blocks;
/// * an entry in the file system directory.
///
/// The file system consists of several data structures:
/// * A bitmap of free disk sectors (cf. `bitmap.h`).
/// * A directory of file names and file headers.
///
/// Both the bitmap and the directory are represented as normal files.  Their
/// file headers are located in specific sectors (sector 0 and sector 1), so
/// that the file system can find them on bootup.
///
/// The file system assumes that the bitmap and directory files are kept
/// “open” continuously while Nachos is running.
///
/// For those operations (such as `Create`, `Remove`) that modify the
/// directory and/or bitmap, if the operation succeeds, the changes are
/// written immediately back to disk (the two files are kept open during all
/// this time).  If the operation fails, and we have modified part of the
/// directory and/or bitmap, we simply discard the changed version, without
/// writing it back to disk.
///
/// Our implementation at this point has the following restrictions:
///
/// * there is no synchronization for concurrent accesses;
/// * files have a fixed size, set when the file is created;
/// * files cannot be bigger than about 3KB in size;
/// * there is no hierarchical directory structure, and only a limited number
///   of files can be added to the system;
/// * there is no attempt to make the system robust to failures (if Nachos
///   exits in the middle of an operation that modifies the file system, it
///   may corrupt the disk).
///
/// Copyright (c) 1992-1993 The Regents of the University of California.
///               2016-2021 Docentes de la Universidad Nacional de Rosario.
/// All rights reserved.  See `copyright.h` for copyright notice and
/// limitation of liability and disclaimer of warranty provisions.


#include "file_system.hh"
#include "directory.hh"
#include "file_header.hh"
#include "lib/bitmap.hh"
#include "threads/system.hh"
#include "threads/lock.hh"

#include <stdio.h>
#include <string.h>

/// Initialize the file system.  If `format == true`, the disk has nothing on
/// it, and we need to initialize the disk to contain an empty directory, and
/// a bitmap of free sectors (with almost but not all of the sectors marked
/// as free).
///
/// If `format == false`, we just have to open the files representing the
/// bitmap and the directory.
///
/// * `format` -- should we initialize the disk?
FileSystem::FileSystem(bool format)
{
    DEBUG('f', "Initializing the file system.\n");
    idxTable = 0;
    idxLocks = 0;
    if (format) {
        Bitmap     *freeMap = new Bitmap(NUM_SECTORS);
        Directory  *dir     = new Directory(NUM_DIR_ENTRIES);
        FileHeader *mapH    = new FileHeader;
        FileHeader *dirH    = new FileHeader;

        // DEBUG('f', "Formatting the file system.\n");

        // First, allocate space for FileHeaders for the directory and bitmap
        // (make sure no one else grabs these!)
        freeMap->Mark(FREE_MAP_SECTOR);
        freeMap->Mark(DIRECTORY_SECTOR);

        // Second, allocate space for the data blocks containing the contents
        // of the directory and bitmap files.  There better be enough space!

        ASSERT(mapH->Allocate(freeMap, FREE_MAP_FILE_SIZE));
        ASSERT(dirH->Allocate(freeMap, DIRECTORY_FILE_SIZE));

        // Flush the bitmap and directory `FileHeader`s back to disk.
        // We need to do this before we can `Open` the file, since open reads
        // the file header off of disk (and currently the disk has garbage on
        // it!).

        // DEBUG('f', "Writing headers back to disk.\n");
        mapH->WriteBack(FREE_MAP_SECTOR);
        dirH->WriteBack(DIRECTORY_SECTOR);

        // OK to open the bitmap and directory files now.
        // The file system operations assume these two files are left open
        // while Nachos is running.

        freeMapFile   = new OpenFile(FREE_MAP_SECTOR);
        directoryFile = new OpenFile(DIRECTORY_SECTOR);

        // Once we have the files “open”, we can write the initial version of
        // each file back to disk.  The directory at this point is completely
        // empty; but the bitmap has been changed to reflect the fact that
        // sectors on the disk have been allocated for the file headers and
        // to hold the file data for the directory and bitmap.

        // DEBUG('f', "Writing bitmap and directory back to disk.\n");
        freeMap->WriteBack(freeMapFile);     // flush changes to disk
        dir->WriteBack(directoryFile);

        if (debug.IsEnabled('f')) {
            freeMap->Print();
            dir->Print();

            delete freeMap;
            delete dir;
            delete mapH;
            delete dirH;
        }
    } else {
        // If we are not formatting the disk, just open the files
        // representing the bitmap and directory; these are left open while
        // Nachos is running.
        Bitmap     *freeMap = new Bitmap(NUM_SECTORS);
        Directory  *dir     = new Directory(NUM_DIR_ENTRIES);
        freeMapFile   = new OpenFile(FREE_MAP_SECTOR);
        directoryFile = new OpenFile(DIRECTORY_SECTOR);
        freeMap->FetchFrom(freeMapFile);
        dir->FetchFrom(directoryFile);
        InitLocksRecursive(DIRECTORY_SECTOR);
    }

    DirLocks* root = new DirLocks;
    root->lock = new Lock("Root lock"); 
    root->sector = DIRECTORY_SECTOR;
    tablaLocks[idxLocks] = root;
    idxLocks++;

    
    lockFreeMap = new Lock("Lock freeMap and Directory");
    lockTablaAbiertos = new Lock("Lock tabla abiertos");
    lockTablaLocks = new Lock("Lock tabla locks");
}

FileSystem::~FileSystem()
{
    delete freeMapFile;
    // delete directoryFile;
    delete lockTablaAbiertos;
    delete lockFreeMap;
    delete lockTablaLocks;
    for(int i=0; i<idxTable; i++) {
        delete tablaAbiertos[i];
    }
    for(int i=0; i<idxLocks; i++) {
        delete tablaLocks[i];
    }
}

void FileSystem::InitLocksRecursive(int sector) {
    Directory *dir = new Directory(NUM_DIR_ENTRIES);
    OpenFile *dirFile = new OpenFile(sector);
    dir->FetchFrom(dirFile);
    const RawDirectory *dirRaw = dir->GetRaw();

    // Crea lock para este directorio si aún no existe
    bool found = false;
    for (int i = 0; i < idxLocks; i++) {
        if (tablaLocks[i]->sector == sector) {
            found = true;
            break;
        }
    }
    if (!found) {
        DirLocks* dirLock = new DirLocks;
        dirLock->lock = new Lock("dirLock");
        dirLock->sector = sector;
        tablaLocks[idxLocks] = dirLock;
        idxLocks++;
    }

    // Recorre subdirectorios
    for (unsigned i = 0; i < dirRaw->tableSize; i++) {
        if (dirRaw->table[i].inUse && dirRaw->table[i].isDir) {
            InitLocksRecursive(dirRaw->table[i].sector);
        }
    }

    delete dirFile;
    delete dir;
}

/// Create a file in the Nachos file system (similar to UNIX `create`).
/// Since we cannot increase the size of files dynamically, we have to give
/// `Create` the initial size of the file.
///
/// The steps to create a file are:
/// 1. Make sure the file does not already exist.
/// 2. Allocate a sector for the file header.
/// 3. Allocate space on disk for the data blocks for the file.
/// 4. Add the name to the directory.
/// 5. Store the new file header on disk.
/// 6. Flush the changes to the bitmap and the directory back to disk.
///
/// Return true if everything goes ok, otherwise, return false.
///
/// Create fails if:
/// * file is already in directory;
/// * no free space for file header;
/// * no free entry for file in directory;
/// * no free space for data blocks for the file.
///
/// Note that this implementation assumes there is no concurrent access to
/// the file system!
///
/// * `name` is the name of file to be created.
/// * `initialSize` is the size of file to be created.
bool
FileSystem::Create(const char *name, unsigned initialSize, int sector)
{
    DEBUG('f', "FileSystem::Create requested\n");
    ASSERT(name != nullptr);
    int lockSector = FindLock(sector);
    tablaLocks[lockSector]->lock->Acquire();

    Bitmap *freeMap = new Bitmap(NUM_SECTORS);

    Directory *dir = new Directory(NUM_DIR_ENTRIES);
    directoryFile = new OpenFile(sector);
    dir->FetchFrom(directoryFile);

    bool success = false;
    int freeSector;

    if (dir->Find(name) != -1) {
        success = false;  // File is already in directory.
        DEBUG('f', "File %s already exists in directory (sector %d).\n", name, sector);
    } else {
        lockFreeMap->Acquire();
        freeMap->FetchFrom(freeMapFile);
        freeSector = freeMap->Find();

        // Find a sector to hold the file header.
        if (freeSector == -1) {
            success = false;  // No free block for file header.
            DEBUG('f', "No free block for file header.\n");
        } else if (!dir->Add(name, freeSector)) {
            success = false;  // No space in directory.
            DEBUG('f', "No space in directory for file %s.\n", name);
        } else {
            FileHeader *h = new FileHeader; 
            success = h->Allocate(freeMap, initialSize); // Fails if no space on disk for data.
            if (success) {
                // Everything worked, flush all changes back to disk.
                h->WriteBack(freeSector);
                dir->WriteBack(directoryFile);
                freeMap->WriteBack(freeMapFile);
            }
            delete h;
        }
        lockFreeMap->Release();
    }

    delete freeMap;
    delete dir;
    delete directoryFile;
    tablaLocks[lockSector]->lock->Release();

    DEBUG('f', "Create finished\n");
    return success;
}

/// Open a file for reading and writing.
///
/// To open a file:
/// 1. Find the location of the file's header, using the directory.
/// 2. Bring the header into memory.
///
/// * `name` is the text name of the file to be opened.
OpenFile *
FileSystem::Open(const char *name, int sector)
{
    DEBUG('f', "FileSystem::Open requested\n");
    ASSERT(name != nullptr);
    int lockSector = FindLock(sector);
    tablaLocks[lockSector]->lock->Acquire();

    Directory *dir = new Directory(NUM_DIR_ENTRIES);
    OpenFile  *openFile = nullptr;

    directoryFile = new OpenFile(sector);
    dir->FetchFrom(directoryFile);
    int fileSector = dir->Find(name);
    if (fileSector >= 0) {
        int i;
        lockTablaAbiertos->Acquire();
        FileData *fd = nullptr;
        for(i=0; i < idxTable && tablaAbiertos[i]->sector != fileSector; i++);
        if (i < idxTable) {
            if (!tablaAbiertos[i]->deleted)
                tablaAbiertos[i]->usedBy++;
            fd = tablaAbiertos[i];
        } else {
            fd = new FileData;
            fd->usedBy = 1;
            fd->sector = fileSector;
            fd->name = name;
            fd->deleted = false;
            fd->lock = new Lock(name);
            tablaAbiertos[idxTable] = fd;
            idxTable++;
        }
        if (!tablaAbiertos[i]->deleted)
            openFile = new OpenFile(fileSector, fd);  // `name` was found in directory.

        lockTablaAbiertos->Release();
    }

    delete dir;
    delete directoryFile;
    tablaLocks[lockSector]->lock->Release();

    DEBUG('f', "Open finished\n");
    return openFile;  // Return null if not found.
}

/// Delete a file from the file system.
///
/// This requires:
/// 1. Remove it from the directory.
/// 2. Delete the space for its header.
/// 3. Delete the space for its data blocks.
/// 4. Write changes to directory, bitmap back to disk.
///
/// Return true if the file was deleted, false if the file was not in the
/// file system.
///
/// * `name` is the text name of the file to be removed.
bool
FileSystem::Remove(const char *name, int sector)
{
    DEBUG('f', "FileSystem::Remove requested\n");

    ASSERT(name != nullptr);
    int lockSector = FindLock(sector);
    tablaLocks[lockSector]->lock->Acquire();

    Directory *dir = new Directory(NUM_DIR_ENTRIES);
    directoryFile = new OpenFile(sector);
    dir->FetchFrom(directoryFile);
    int fileSector = dir->Find(name);
    if (fileSector == -1) {
        delete dir;
        tablaLocks[lockSector]->lock->Release();
        return false;  // file not found
    }
    FileHeader *fileH = new FileHeader;
    fileH->FetchFrom(fileSector);

    int i;
    lockTablaAbiertos->Acquire();
    for (i=0; i<idxTable && tablaAbiertos[i]->sector == fileSector; i++);
    if (tablaAbiertos[i] != nullptr) {
        tablaAbiertos[i]->deleted = true;
        if (tablaAbiertos[i]->usedBy == 0) {
            lockFreeMap->Acquire();
            Bitmap *freeMap = new Bitmap(NUM_SECTORS);
            freeMap->FetchFrom(freeMapFile);

            fileH->Deallocate(freeMap);  // Remove data blocks.
            freeMap->Clear(fileSector);      // Remove header block.

            freeMap->WriteBack(freeMapFile);  // Flush to disk.

            lockFreeMap->Release();
            delete freeMap;
        }
    } else {
        lockFreeMap->Acquire();
        Bitmap *freeMap = new Bitmap(NUM_SECTORS);
        freeMap->FetchFrom(freeMapFile);

        fileH->Deallocate(freeMap);  // Remove data blocks.
        freeMap->Clear(fileSector);      // Remove header block.

        freeMap->WriteBack(freeMapFile);  // Flush to disk.

        lockFreeMap->Release();
        delete freeMap;
    }
    lockTablaAbiertos->Release();

    dir->Remove(name);
    dir->WriteBack(directoryFile);    // Flush to disk.

    delete directoryFile;
    delete fileH;
    delete dir;
    tablaLocks[lockSector]->lock->Release();
    DEBUG('f', "Remove finished\n");

    return true;
}

/// List all the files in the file system directory.
void
FileSystem::List(int sector)
{
    DEBUG('f', "FileSystem::List requested\n");
    Directory *dir = new Directory(NUM_DIR_ENTRIES);
    directoryFile = new OpenFile(sector);

    dir->FetchFrom(directoryFile);
    dir->List();
    delete directoryFile;
    delete dir;
    DEBUG('f', "List finished\n");
}

static bool
AddToShadowBitmap(unsigned sector, Bitmap *map)
{
    ASSERT(map != nullptr);

    if (map->Test(sector)) {
        DEBUG('f', "Sector %u was already marked.\n", sector);
        return false;
    }
    map->Mark(sector);
    DEBUG('f', "Marked sector %u.\n", sector);
    return true;
}

static bool
CheckForError(bool value, const char *message)
{
    if (!value) {
        DEBUG('f', "Error: %s\n", message);
    }
    return !value;
}

static bool
CheckSector(unsigned sector, Bitmap *shadowMap)
{
    if (CheckForError(sector < NUM_SECTORS,
                      "sector number too big.  Skipping bitmap check.")) {
        return true;
    }
    return CheckForError(AddToShadowBitmap(sector, shadowMap),
                         "sector number already used.");
}

static bool
CheckFileHeader(const RawFileHeader *rh, unsigned num, Bitmap *shadowMap)
{
    ASSERT(rh != nullptr);

    bool error = false;

    DEBUG('f', "Checking file header %u.  File size: %u bytes, number of sectors: %u.\n",
          num, rh->numBytes, rh->numSectors);
    error |= CheckForError(rh->numSectors >= DivRoundUp(rh->numBytes,
                                                        SECTOR_SIZE),
                           "sector count not compatible with file size.");
    error |= CheckForError(rh->numSectors < NUM_DIRECT,
                           "too many blocks.");
    for (unsigned i = 0; i < rh->numSectors; i++) {
        unsigned s = rh->dataSectors[i];
        error |= CheckSector(s, shadowMap);
    }
    return error;
}

static bool
CheckBitmaps(const Bitmap *freeMap, const Bitmap *shadowMap)
{
    bool error = false;
    for (unsigned i = 0; i < NUM_SECTORS; i++) {
        DEBUG('f', "Checking sector %u. Original: %u, shadow: %u.\n",
              i, freeMap->Test(i), shadowMap->Test(i));
        error |= CheckForError(freeMap->Test(i) == shadowMap->Test(i),
                               "inconsistent bitmap.");
    }
    return error;
}

static bool
CheckDirectory(const RawDirectory *rd, Bitmap *shadowMap)
{
    ASSERT(rd != nullptr);
    ASSERT(shadowMap != nullptr);

    bool error = false;
    unsigned nameCount = 0;
    const char *knownNames[NUM_DIR_ENTRIES];

    for (unsigned i = 0; i < NUM_DIR_ENTRIES; i++) {
        DEBUG('f', "Checking direntry: %u.\n", i);
        const DirectoryEntry *e = &rd->table[i];

        if (e->inUse) {
            if (strlen(e->name) > FILE_NAME_MAX_LEN) {
                DEBUG('f', "Filename too long.\n");
                error = true;
            }

            // Check for repeated filenames.
            DEBUG('f', "Checking for repeated names.  Name count: %u.\n",
                  nameCount);
            bool repeated = false;
            for (unsigned j = 0; j < nameCount; j++) {
                DEBUG('f', "Comparing \"%s\" and \"%s\".\n",
                      knownNames[j], e->name);
                if (strcmp(knownNames[j], e->name) == 0) {
                    DEBUG('f', "Repeated filename.\n");
                    repeated = true;
                    error = true;
                }
            }
            if (!repeated) {
                knownNames[nameCount] = e->name;
                DEBUG('f', "Added \"%s\" at %u.\n", e->name, nameCount);
                nameCount++;
            }

            // Check sector.
            error |= CheckSector(e->sector, shadowMap);

            // Check file header.
            FileHeader *h = new FileHeader;
            const RawFileHeader *rh = h->GetRaw();
            h->FetchFrom(e->sector);
            error |= CheckFileHeader(rh, e->sector, shadowMap);
            delete h;
        }
    }
    return error;
}

bool
FileSystem::Check()
{
    DEBUG('f', "Performing filesystem check\n");
    bool error = false;
    directoryFile = new OpenFile(DIRECTORY_SECTOR);
    Bitmap *shadowMap = new Bitmap(NUM_SECTORS);
    shadowMap->Mark(FREE_MAP_SECTOR);
    shadowMap->Mark(DIRECTORY_SECTOR);

    DEBUG('f', "Checking bitmap's file header.\n");

    FileHeader *bitH = new FileHeader;
    const RawFileHeader *bitRH = bitH->GetRaw();
    bitH->FetchFrom(FREE_MAP_SECTOR);
    DEBUG('f', "  File size: %u bytes, expected %u bytes.\n"
               "  Number of sectors: %u, expected %u.\n",
          bitRH->numBytes, FREE_MAP_FILE_SIZE,
          bitRH->numSectors, FREE_MAP_FILE_SIZE / SECTOR_SIZE);
    error |= CheckForError(bitRH->numBytes == FREE_MAP_FILE_SIZE,
                           "bad bitmap header: wrong file size.");
    error |= CheckForError(bitRH->numSectors == FREE_MAP_FILE_SIZE / SECTOR_SIZE,
                           "bad bitmap header: wrong number of sectors.");
    error |= CheckFileHeader(bitRH, FREE_MAP_SECTOR, shadowMap);
    delete bitH;

    DEBUG('f', "Checking directory.\n");

    FileHeader *dirH = new FileHeader;
    const RawFileHeader *dirRH = dirH->GetRaw();
    dirH->FetchFrom(DIRECTORY_SECTOR);
    error |= CheckFileHeader(dirRH, DIRECTORY_SECTOR, shadowMap);
    delete dirH;

    Bitmap *freeMap = new Bitmap(NUM_SECTORS);
    freeMap->FetchFrom(freeMapFile);
    Directory *dir = new Directory(NUM_DIR_ENTRIES);
    const RawDirectory *rdir = dir->GetRaw();
    dir->FetchFrom(directoryFile);
    error |= CheckDirectory(rdir, shadowMap);
    delete dir;

    // The two bitmaps should match.
    DEBUG('f', "Checking bitmap consistency.\n");
    error |= CheckBitmaps(freeMap, shadowMap);
    delete shadowMap;
    delete freeMap;

    DEBUG('f', error ? "Filesystem check failed.\n"
                     : "Filesystem check succeeded.\n");

    return !error;
}

/// Print everything about the file system:
/// * the contents of the bitmap;
/// * the contents of the directory;
/// * for each file in the directory:
///   * the contents of the file header;
///   * the data in the file.
void
FileSystem::Print(int sector)
{
    FileHeader *bitH    = new FileHeader;
    FileHeader *dirH    = new FileHeader;
    Bitmap     *freeMap = new Bitmap(NUM_SECTORS);
    Directory  *dir     = new Directory(NUM_DIR_ENTRIES);
    directoryFile = new OpenFile(sector);

    printf("--------------------------------\n");
    bitH->FetchFrom(FREE_MAP_SECTOR);
    bitH->Print("Bitmap");

    printf("--------------------------------\n");
    dirH->FetchFrom(DIRECTORY_SECTOR);
    dirH->Print("Directory");

    printf("--------------------------------\n");
    freeMap->FetchFrom(freeMapFile);
    freeMap->Print();

    printf("--------------------------------\n");
    dir->FetchFrom(directoryFile);
    dir->Print();
    printf("--------------------------------\n");

    delete bitH;
    delete dirH;
    delete freeMap;
    delete dir;
}

bool 
FileSystem::Expand(FileHeader *hdr, unsigned size) {
    DEBUG('f', "FileSystem::Expand requested\n");

    ASSERT(hdr != nullptr);
    ASSERT(size != 0);

    lockFreeMap->Acquire();
    Bitmap *freeMap = new Bitmap(NUM_SECTORS);
    freeMap->FetchFrom(freeMapFile);
    bool tmp = hdr->Expand(freeMap, size);
    if(tmp) freeMap->WriteBack(freeMapFile);
    lockFreeMap->Release();
    DEBUG('f', "Expand finished\n");
    return tmp;
}

void 
FileSystem::closeFile(int sector) {
    DEBUG('f', "FileSystem::CloseFile requested\n");

    lockTablaAbiertos->Acquire();
    if(sector != 0 && sector != 1) {
        int i;
        for (i=0; i<idxTable && !(tablaAbiertos[i]->sector == sector); i++);
        tablaAbiertos[i]->usedBy--;
        if(tablaAbiertos[i]->deleted)
            Remove(tablaAbiertos[i]->name);
    }
    lockTablaAbiertos->Release();
    DEBUG('f', "CloseFile finished\n");
}

int
FileSystem::Cd(char* path) {
    DEBUG('f', "FileSystem::Cd requested\n");

    Directory *dir = new Directory(NUM_DIR_ENTRIES);
    OpenFile* workingDir;
    int sector;

    if (path[0] == '/') {
        sector = DIRECTORY_SECTOR;
        path++; // Salta el primer '/'
    } else {
        sector = currentThread->GetCurrentDir();
    }
    workingDir = new OpenFile(sector);

    char buff[256];
    strcpy(buff, path);
    char *dirName = strtok(buff, "/");

    for (int i = 0; dirName != NULL && sector != -1; i++) {
        dir->FetchFrom(workingDir);
        sector = dir->Find(dirName, true);
        DEBUG('f', "Cd: looking for directory %s in sector %d\n", dirName, sector);
        if (sector != -1) {
            delete workingDir;
            dirName = strtok(NULL, "/");
            if (dirName != NULL)
                workingDir = new OpenFile(sector);
        }
    }
    delete dir;
    DEBUG('f', "Cd finished (sector %d)\n", sector);
    return sector;
}

void
FileSystem::Ls() {
    DEBUG('f', "FileSystem::Ls requested on sector %d by %s\n", currentThread->GetCurrentDir(), currentThread->GetName());
    Directory *dir = new Directory(NUM_DIR_ENTRIES);
    OpenFile* workingDir = new OpenFile(currentThread->GetCurrentDir());

    dir->FetchFrom(workingDir);
    dir->List();

    delete dir;
    delete workingDir;
    DEBUG('f', "Ls finished\n");
}

bool
FileSystem::Mkdir(char* name) {
    DEBUG('f', "FileSystem::Mkdir requested on sector %d by %s\n", currentThread->GetCurrentDir(), currentThread->GetName());
    int currDir = currentThread->GetCurrentDir();
    tablaLocks[FindLock(currDir)]->lock->Acquire();

    /* Buscamos si hay espacio para guardar el header */
    lockFreeMap->Acquire();
    Bitmap *freeMap = new Bitmap(NUM_SECTORS);
    freeMap->FetchFrom(freeMapFile);
    int hdrSector = freeMap->Find();
    if (hdrSector == -1) {
        tablaLocks[FindLock(currDir)]->lock->Release();
        lockFreeMap->Release();
        delete freeMap;
        return false;
    }

    /* Reservamos el espacio del nuevo directorio en disco */
    FileHeader *dirH = new FileHeader;
    if (!dirH->Allocate(freeMap, DIRECTORY_FILE_SIZE)) {
        tablaLocks[FindLock(currDir)]->lock->Release();
        lockFreeMap->Release();
        delete freeMap;
        delete dirH;
        return false;
    }
    freeMap->WriteBack(freeMapFile);
    lockFreeMap->Release();
    DEBUG('f', "Created and stored directory header\n");

    /* Agregamos el directorio como sub directorio del actual */
    Directory *currentDir = new Directory(NUM_DIR_ENTRIES);
    OpenFile *currentDirFile = new OpenFile(currDir);
    currentDir->FetchFrom(currentDirFile);
    if(!currentDir->Add(name, hdrSector, true)) {
        lockFreeMap->Acquire();
        freeMap->FetchFrom(freeMapFile);
        freeMap->Clear(hdrSector);
        freeMap->WriteBack(freeMapFile);
        lockFreeMap->Release();
        delete freeMap;
        delete dirH;
        delete currentDir;
        delete currentDirFile;
        tablaLocks[FindLock(currDir)]->lock->Release();
        return false;
    }
    DEBUG('f', "Added entry for new directory\n");

    // Make a lock for directory
    lockTablaLocks->Acquire();
    if(idxLocks == MAX_FILE_AMMOUNT) {
        DEBUG('f', "No more space in lockTable\n");
        lockFreeMap->Acquire();
        freeMap->FetchFrom(freeMapFile);
        freeMap->Clear(hdrSector);
        freeMap->WriteBack(freeMapFile);
        lockFreeMap->Release();
        delete freeMap;
        delete dirH;
        delete currentDir;
        delete currentDirFile;
        lockTablaLocks->Release();
        tablaLocks[FindLock(currDir)]->lock->Release();
        return false;
    }
    DirLocks* dirL = new DirLocks;
    dirL->sector = hdrSector;
    dirL->lock = new Lock("dirLock");
    tablaLocks[idxLocks] = dirL;
    idxLocks++;
    lockTablaLocks->Release();

    /* Guardamos los cambios en el disco */
    currentDir->WriteBack(currentDirFile);
    dirH->WriteBack(hdrSector);

    delete freeMap;
    delete dirH;
    delete currentDir;
    tablaLocks[FindLock(currDir)]->lock->Release();

    /* Escribimos \0 en todo el archivo */
    OpenFile *openFile = Open(name, currDir);
    char *buffer = new char[SECTOR_SIZE];
    memset(buffer, 0, SECTOR_SIZE);
    for (unsigned i = 0; i < DIRECTORY_FILE_SIZE; i += sizeof(buffer)) {
        openFile->Write(buffer, sizeof(buffer));
    }

    DEBUG('f', "Mkdir finished\n");
    return true;
}

int
FileSystem::FindLock(int sector) {
    int i;
    // DEBUG('f', "Looking for lock of directory in sector %d\n", sector);
    for(i = 0; i < idxLocks && tablaLocks[i]->sector != sector; i++);
    // DEBUG('f', "idxLocks = %d, i = %d\n", idxLocks, i);
    if(i == idxLocks) {
        i = -1;
        // DEBUG('f', "Couldn't find lock for directory sector\n");
    }
    return i;
}