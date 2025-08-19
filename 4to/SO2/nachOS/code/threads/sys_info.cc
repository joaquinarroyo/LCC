#include "sys_info.hh"
#include "copyright.h"
#include "filesys/directory_entry.hh"
#include "filesys/file_system.hh"
#include "filesys/raw_file_header.hh"

#include "machine/mmu.hh"

#include <stdio.h>


void SysInfo()
{
    (void) COPYRIGHT;  // Prevent warning about unused variable.

    const char *OPTIONS =
#ifdef THREADS
      "THREADS "
#endif
#ifdef USER_PROGRAM
      "USER_PROGRAM "
#endif
#ifdef VMEM
      "VMEM "
#endif
#ifdef FILESYS
      "FILESYS "
#endif
#ifdef FILESYS_STUB
      "FILESYS_STUB "
#endif
#ifdef NETWORK
      "NETWORK "
#endif
#ifdef USE_TLB
      "USE_TLB "
#endif
#ifdef FILESYS_NEEDED
      "FILESYS_NEEDED "
#endif
#ifdef DFS_TICKS_FIX
      "DFS_TICKS_FIX "
#endif
      ;

    printf("System information.\n");
    printf("\n\
General:\n\
  Nachos release: %s %s.\n\
  Option definitions: %s\n",
      PROGRAM, VERSION, OPTIONS);
    printf("\n\
Memory:\n\
  Page size: %d bytes.\n\
  Number of pages: %d.\n\
  Number of TLB entries: %d.\n\
  Memory size: %d bytes.\n",
      PAGE_SIZE, NUM_PHYS_PAGES, TLB_SIZE, MEMORY_SIZE);
    printf("\n\
Disk:\n\
  Sector size: %d bytes.\n\
  Sectors per track: %d.\n\
  Number of tracks: %d.\n\
  Number of sectors: %d.\n\
  Disk size: %d bytes.\n",
      SECTOR_SIZE, SECTORS_PER_TRACK, NUM_TRACKS, NUM_SECTORS, NUM_SECTORS*SECTOR_SIZE);
    printf("\n\
Filesystem:\n\
  Sectors per header: %u.\n\
  Maximum file size: %u bytes.\n\
  File name maximum length: %u.\n\
  Free sectors map size: %u bytes.\n\
  Maximum number of dir-entries: %u.\n\
  Directory file size: %u bytes.\n",
      NUM_DIRECT, MAX_FILE_SIZE, FILE_NAME_MAX_LEN,
      FREE_MAP_FILE_SIZE, NUM_DIR_ENTRIES, DIRECTORY_FILE_SIZE);
}
