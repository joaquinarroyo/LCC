module Extra.Error
  ( Error(..)
  ) where

-- Estructura para errores
data Error
  = WrongDateFormat
  | BadPriority
  | FilterError
  | DirNotFound
  | TaskNotFound
  | TaskAlreadyExists
  | DirAlreadyExists
  | CannotEditRootDir
  | CannotCreateTaskInRootDir
  | ProfileDoesNotExists
  | ProfileAlreadyExists
  | ErrorLoadingProfile
  | CannotDeleteDefaultProfile
  deriving (Eq)

instance Show Error where
  show WrongDateFormat = "Wrong date format: YYYY-MM-DD [HH:MM]"
  show BadPriority = "Bad priority: must be >= -1"
  show FilterError = "Filter error"
  show DirNotFound = "Directory not found"
  show TaskNotFound = "Task not found"
  show TaskAlreadyExists = "Task already exists"
  show DirAlreadyExists = "Directory already exists"
  show CannotEditRootDir = "Cannot edit root directory"
  show CannotCreateTaskInRootDir = "Cannot create task in root directory"
  show ProfileDoesNotExists = "Profile does not exists"
  show ProfileAlreadyExists = "Profile already exists"
  show ErrorLoadingProfile = "Error loading profile"
  show CannotDeleteDefaultProfile = "Cannot delete default profile"
