module Racket.Filesystem

import Data.Maybe
import Ffiglet.FFI
import Racket.Basics
import Racket.Exceptions
import Racket.Hashes
import Racket.Lists
import Racket.Parameters

--- Exceptions!

-- exn:fail:filesystem

export
interface IsExnFail e => IsExnFailFilesystem (e : Type) where

export
%foreign "scheme,racket:exn:fail:filesystem?"
prim__isExnFailFilesystem : AnyPtr -> Bool

export
isExnFailFilesystem : t -> Bool
isExnFailFilesystem = prim__isExnFailFilesystem . believe_me

export
data ExnFailFilesystem : Type where [external]

export
IsExn ExnFailFilesystem where

export
IsExnFail ExnFailFilesystem where

export
IsExnFailFilesystem ExnFailFilesystem where

-- exn:fail:filesystem:exists

export
interface IsExnFailFilesystem e => IsExnFailFilesystemExists (e : Type) where

%foreign "scheme,racket:exn:fail:filesystem:exists?"
prim__isExnFailFilesystemExists : AnyPtr -> Bool

export
isExnFailFilesystemExists : t -> Bool
isExnFailFilesystemExists = prim__isExnFailFilesystemExists . believe_me

export
data ExnFailFilesystemExists : Type where [external]

export
IsExn ExnFailFilesystemExists where

export
IsExnFail ExnFailFilesystemExists where

export
IsExnFailFilesystem ExnFailFilesystemExists where

export
IsExnFailFilesystemExists ExnFailFilesystemExists where

-- exn:fail:filesystem:version

export
interface IsExnFailFilesystem e => IsExnFailFilesystemVersion (e : Type) where

%foreign "scheme,racket:exn:fail:filesystem:version?"
prim__isExnFailFilesystemVersion : AnyPtr -> Bool

export
isExnFailFilesystemVersion : t -> Bool
isExnFailFilesystemVersion = prim__isExnFailFilesystemVersion . believe_me

export
data ExnFailFilesystemVersion : Type where [external]

export
IsExn ExnFailFilesystemVersion where

export
IsExnFail ExnFailFilesystemVersion where

export
IsExnFailFilesystem ExnFailFilesystemVersion where

export
IsExnFailFilesystemVersion ExnFailFilesystemVersion where

-- exn:fail:filesystem:errno

export
interface IsExnFailFilesystem e => IsExnFailFilesystemErrno (e : Type) where

%foreign "scheme,racket:exn:fail:filesystem:errno?"
prim__isExnFailFilesystemErrno : AnyPtr -> Bool

export
isExnFailFilesystemErrno : t -> Bool
isExnFailFilesystemErrno = prim__isExnFailFilesystemErrno . believe_me

export
data ExnFailFilesystemErrno : Type where [external]

export
IsExn ExnFailFilesystemErrno where

export
IsExnFail ExnFailFilesystemErrno where

export
IsExnFailFilesystem ExnFailFilesystemErrno where

export
IsExnFailFilesystemErrno ExnFailFilesystemErrno where

-- exn:fail:filesystem:missing-module

export
interface IsExnFailFilesystem e => IsExnFailFilesystemMissingModule (e : Type) where

%foreign "scheme,racket:exn:fail:filesystem:missing-module?"
prim__isExnFailFilesystemMissingModule : AnyPtr -> Bool

export
isExnFailFilesystemMissingModule : t -> Bool
isExnFailFilesystemMissingModule = prim__isExnFailFilesystemMissingModule . believe_me

export
data ExnFailFilesystemMissingModule : Type where [external]

export
IsExn ExnFailFilesystemMissingModule where

export
IsExnFail ExnFailFilesystemMissingModule where

export
IsExnFailFilesystem ExnFailFilesystemMissingModule where

export
IsExnFailFilesystemMissingModule ExnFailFilesystemMissingModule where


--- Actual useful code.



public export
data FilePath : Type where [external]

%foreign "scheme,racket:path?"
prim__isFilePath : AnyPtr -> Bool

export
isFilePath : t -> Bool
isFilePath = prim__isFilePath . believe_me

export
SafeCast FilePath where
  safeCast ptr = if isFilePath ptr then Just (believe_me ptr) else Nothing

%foreign "racket,scheme:find-executable-path"
prim__findExecutablePath : (program : AnyPtr) -> (related : AnyPtr) -> (deepest : AnyPtr) -> PrimIO AnyPtr

export
findExecutablePath : HasIO io => String -> io (Maybe FilePath)
findExecutablePath p = let false = believe_me False in
  safeCast <$> primIO (prim__findExecutablePath (believe_me p) false false)

export
findExecutablePath' : HasIO io => String -> Maybe FilePath -> Bool -> io (Maybe FilePath)
findExecutablePath' p r d =
  let act = prim__findExecutablePath (believe_me p) (believe_me r) (believe_me d) in
  safeCast <$> primIO act
  
-- fileExists

%foreign "racket,scheme:file-exists?"
prim__fileExists : AnyPtr -> PrimIO Bool

export
fileExists : HasIO io => FilePath -> io Bool
fileExists p = primIO $ prim__fileExists (believe_me p)

-- directoryExists

%foreign "racket,scheme:directory-exists?"
prim__directoryExists : AnyPtr -> PrimIO Bool

export
directoryExists : HasIO io => FilePath -> io Bool
directoryExists p = primIO $ prim__directoryExists (believe_me p)

-- linkExists

%foreign "racket,scheme:link-exists?"
prim__linkExists : AnyPtr -> PrimIO Bool

export
linkExists : HasIO io => FilePath -> io Bool
linkExists p = primIO $ prim__linkExists (believe_me p)

--file-or-directory-type

-- deleteFile

%foreign "scheme,racket:delete-file"
prim__deleteFile : AnyPtr -> PrimIO AnyPtr

export
deleteFile : HasIO io => FilePath -> io (Either ExnFailFilesystem ())
deleteFile p = defang isExnFailFilesystem $ prim__deleteFile (believe_me p)

-- deleteDirectory

%foreign "scheme,racket:delete-directory"
prim__deleteDirectory : AnyPtr -> PrimIO AnyPtr

export
deleteDirectory : HasIO io => FilePath -> io (Either ExnFailFilesystem ())
deleteDirectory p = defang isExnFailFilesystem $ prim__deleteDirectory (believe_me p)

%foreign "scheme,racket:rename-file-or-directory"
prim__renameFileOrDirectory : AnyPtr -> AnyPtr -> Bool -> PrimIO AnyPtr

export
renameFileOrDirectory : HasIO io => FilePath -> FilePath -> Bool -> io (Either ExnFailFilesystem ())
renameFileOrDirectory old new ex = defang isExnFailFilesystem $
  prim__renameFileOrDirectory (believe_me old) (believe_me new) ex

%foreign "scheme,racket:file-or-directory-modified-seconds"
prim__fileOrDirectoryModifySeconds : AnyPtr -> PrimIO AnyPtr

export
fileOrDirectoryModifySeconds : HasIO io => FilePath -> io (Either ExnFailFilesystem Int)
fileOrDirectoryModifySeconds path = defang isExnFailFilesystem $
  prim__fileOrDirectoryModifySeconds (believe_me path)

%foreign "scheme,racket:file-or-directory-permissions"
prim__fileOrDirectoryPermissions : AnyPtr -> AnyPtr -> PrimIO AnyPtr

export
fileOrDirectoryPermissions : HasIO io => FilePath -> io (Either ExnFailFilesystem Int)
fileOrDirectoryPermissions path = defang isExnFailFilesystem $
  prim__fileOrDirectoryPermissions (believe_me path) (believe_me $ symbol "bits")

export
setFileOrDirectoryPermissions : HasIO io => FilePath -> Int -> io (Either ExnFailFilesystem ())
setFileOrDirectoryPermissions path perms = defang isExnFailFilesystem $
  prim__fileOrDirectoryPermissions (believe_me path) (believe_me perms)

%foreign "scheme,racket:file-size"
prim__fileSize : AnyPtr -> PrimIO AnyPtr

export
fileSize : HasIO io => FilePath -> io (Either ExnFailFilesystem Int)
fileSize path = defang isExnFailFilesystem $
  prim__fileSize (believe_me path)

%foreign "scheme,racket:copy-file"
prim__copyFile : AnyPtr -> AnyPtr -> Bool -> PrimIO AnyPtr

export
copyFile : HasIO io => (src : FilePath) -> (dest : FilePath) -> (existsOk: Bool) -> io (Either ExnFailFilesystem Int)
copyFile src dest existsOk = defang isExnFailFilesystem $
  prim__copyFile (believe_me src) (believe_me src) existsOk

%foreign "scheme,racket:copy-file"
prim__makeFileOrDirectoryLink : AnyPtr -> AnyPtr -> PrimIO AnyPtr

export
makeFileOrDirectoryLink : HasIO io => (src : FilePath) -> (dest : FilePath) -> io (Either ExnFailFilesystem Int)
makeFileOrDirectoryLink src dest = defang isExnFailFilesystem $
  prim__makeFileOrDirectoryLink (believe_me src) (believe_me src)


%foreign "scheme,racket:(lambda () current-directory)"
prim__currentDirectory : PrimIO (Parameter FilePath)

export
currentDirectory : HasIO io => io (Parameter FilePath)
currentDirectory = primIO prim__currentDirectory

export
getCurrentDirectory : HasIO io => io FilePath
getCurrentDirectory = currentDirectory >>= readParameter

export
setCurrentDirectory : HasIO io => FilePath -> io ()
setCurrentDirectory e = currentDirectory >>= \f => writeParameter f e

%foreign "scheme,racket:(lambda (path build?) (directory-list path #:build? build?))"
prim__directoryList : AnyPtr -> Bool -> PrimIO AnyPtr

export
directoryList : HasIO io => FilePath -> Bool -> io (Either ExnFailFilesystem (Conses FilePath))
directoryList path build = defang isExnFailFilesystem $
  prim__directoryList (believe_me path) (believe_me build)

export
data FilesystemChangeEvent : Type where [external]

%foreign "scheme,racket:filesystem-change-evt?"
prim__isFilesystemChangeEvent : AnyPtr -> Bool

export
isFilesystemChangeEvent : t -> Bool
isFilesystemChangeEvent = prim__isFilesystemChangeEvent . believe_me

-- just for fun, this can actually raise ExnFailUnsupported too, if your OS doesn't support it. But we're not going to
-- attempt to catch that because it's more complicated and we don't have a backup yet in birb.
%foreign "scheme,racket:filesystem-change-evt"
prim__filesystemChangeEvent : AnyPtr -> PrimIO AnyPtr

export
filesystemChangeEvent : HasIO io => FilePath -> io (Either ExnFailFilesystem FilesystemChangeEvent)
filesystemChangeEvent path = defang isExnFailFilesystem $
  prim__filesystemChangeEvent (believe_me path)

||| FilesystemChangeEvent, but indexed by the FilePath it refers to
export
data FilePathChangeEvent : FilePath -> Type where [external]

filePathChangeEvent : HasIO io => (p : FilePath) -> io (Either ExnFailFilesystem (FilePathChangeEvent p))
filePathChangeEvent path = defang isExnFailFilesystem $
  prim__filesystemChangeEvent (believe_me path)

%foreign "scheme,racket:(lambda () file-type-bits)"
prim__fileTypeBits : Int

%foreign "scheme,racket:(lambda () socket-type-bits)"
prim__socketTypeBits : Int

%foreign "scheme,racket:(lambda () symbolic-link-type-bits)"
prim__symbolicLinkTypeBits : Int

%foreign "scheme,racket:(lambda () regular-file-type-bits)"
prim__regularFileTypeBits : Int

%foreign "scheme,racket:(lambda () block-device-type-bits)"
prim__blockDeviceTypeBits : Int
%foreign "scheme,racket:(lambda () directory-type-bits)"
prim__directoryTypeBits : Int
%foreign "scheme,racket:(lambda () character-device-type-bits)"
prim__characterDeviceTypeBits : Int
%foreign "scheme,racket:(lambda () fifo-type-bits)"
prim__fifoTypeBits : Int
%foreign "scheme,racket:(lambda () set-user-id-bit)"
prim__setUserIdBit : Int
%foreign "scheme,racket:(lambda () set-group-id-bit)"
prim__setGroupIdBit : Int
%foreign "scheme,racket:(lambda () sticky-bit)"
prim__stickyBit : Int
%foreign "scheme,racket:(lambda () user-permission-bits)"
prim__userPermissionBits : Int
%foreign "scheme,racket:(lambda () user-read-bit)"
prim__userReadBit : Int
%foreign "scheme,racket:(lambda () user-write-bit)"
prim__userWriteBit : Int
%foreign "scheme,racket:(lambda () user-execute-bit)"
prim__userExecuteBit : Int

%foreign "scheme,racket:(lambda () group-permission-bits)"
prim__groupPermissionBits : Int
%foreign "scheme,racket:(lambda () group-read-bit)"
prim__groupReadBit : Int
%foreign "scheme,racket:(lambda () group-write-bit)"
prim__groupWriteBit : Int
%foreign "scheme,racket:(lambda () group-execute-bit)"
prim__groupExecuteBit : Int

%foreign "scheme,racket:(lambda () other-permission-bits)"
prim__otherPermissionBits : Int
%foreign "scheme,racket:(lambda () other-read-bit)"
prim__otherReadBit : Int
%foreign "scheme,racket:(lambda () other-write-bit)"
prim__otherWriteBit : Int
%foreign "scheme,racket:(lambda () other-execute-bit)"
prim__otherExecuteBit : Int

data FileType
  = RegularFile
  | Directory
  | Socket
  | SymbolicLink
  | CharacterDevice
  | BlockDevice
  | Fifo
  -- Now we leave the realms of sanity and are into the realms of OS-specific POSIX
  -- extensions. Wikipedia documents only that Solaris has 'doors' (which were new to me as a
  -- non-solaris user) and nothing else. In any case, it's going to have to be up to the user to
  -- figure it out because we don't have any of the bits available in racket to test it.
  | EldritchHorror

public export
record FileMode where
  constructor MkFileMode
  fileType : FileType
  userR  : Bool
  userW  : Bool
  userX  : Bool
  groupR : Bool
  groupW : Bool
  groupX : Bool
  otherR : Bool
  otherW : Bool
  otherX : Bool
  setUid : Bool
  setGid : Bool
  sticky : Bool
  rawMode : Int
  

isBitSet : Int -> Int -> Bool
isBitSet b c = prim__and_Int b c /= 0

filetype : Int -> FileType
filetype mode =
  if      isBitSet mode prim__regularFileTypeBits     then RegularFile
  else if isBitSet mode prim__directoryTypeBits       then Directory
  else if isBitSet mode prim__socketTypeBits          then Socket
  else if isBitSet mode prim__symbolicLinkTypeBits    then SymbolicLink
  else if isBitSet mode prim__characterDeviceTypeBits then CharacterDevice
  else if isBitSet mode prim__blockDeviceTypeBits     then BlockDevice
  else if isBitSet mode prim__fifoTypeBits            then Fifo
  else EldritchHorror

modeify : Int -> FileMode
modeify i = MkFileMode
  (filetype i)
  (isBitSet i prim__userReadBit) 
  (isBitSet i prim__userWriteBit) 
  (isBitSet i prim__userExecuteBit) 
  (isBitSet i prim__groupReadBit) 
  (isBitSet i prim__groupWriteBit) 
  (isBitSet i prim__groupExecuteBit) 
  (isBitSet i prim__otherReadBit) 
  (isBitSet i prim__otherWriteBit) 
  (isBitSet i prim__otherExecuteBit) 
  (isBitSet i prim__setUserIdBit) 
  (isBitSet i prim__setGroupIdBit) 
  (isBitSet i prim__stickyBit) 
  i

public export
record Stat where
  constructor MkStat
  mode         : FileMode
  inode        : Int
  uid          : Int
  gid          : Int
  size         : Int
  blockSize    : Int
  blockCount   : Int
  linkCount    : Int
  deviceID     : Int
  atimeSecs    : Int
  atimeNanos   : Int
  ctimeSecs    : Int
  ctimeNanos   : Int
  mtimeSecs    : Int
  mtimeNanos   : Int
  createdSecs  : Int
  createdNanos : Int
  specialFileDeviceId : Int

statify : Hash Symbol Int -> Stat
statify hash = MkStat
  (modeify $ fromMaybe 0 $ hashRef (symbol "mode") hash)
  (fromMaybe 0 $ hashRef (symbol "inode") hash)
  (fromMaybe 0 $ hashRef (symbol "user-id") hash)
  (fromMaybe 0 $ hashRef (symbol "group-id") hash)
  (fromMaybe 0 $ hashRef (symbol "size") hash)
  (fromMaybe 0 $ hashRef (symbol "block-size") hash)
  (fromMaybe 0 $ hashRef (symbol "block-count") hash)
  (fromMaybe 0 $ hashRef (symbol "hardlink-count") hash)
  (fromMaybe 0 $ hashRef (symbol "device-id") hash)
  (fromMaybe 0 $ hashRef (symbol "access-time-seconds") hash)
  (fromMaybe 0 $ hashRef (symbol "access-time-nanoseconds") hash)
  (fromMaybe 0 $ hashRef (symbol "change-time-seconds") hash)
  (fromMaybe 0 $ hashRef (symbol "change-time-nanoseconds") hash)
  (fromMaybe 0 $ hashRef (symbol "modify-time-seconds") hash)
  (fromMaybe 0 $ hashRef (symbol "modify-time-nanoseconds") hash)
  (fromMaybe 0 $ hashRef (symbol "creation-time-seconds") hash)
  (fromMaybe 0 $ hashRef (symbol "creation-time-nanoseconds") hash)
  (fromMaybe 0 $ hashRef (symbol "device-id-for-special-file") hash)

%foreign "scheme,racket:file-or-directory-stat"
prim__fileOrDirectoryStat : AnyPtr -> Bool -> PrimIO AnyPtr

-- That was rather a lot of work to write this function...
export
fileOrDirectoryStat : HasIO io => String -> Bool -> io (Either ExnFailFilesystem Stat)
fileOrDirectoryStat fp link =
  let action = prim__fileOrDirectoryStat (believe_me . show $ fp) link in
  map statify <$> defang prim__isExnFailFilesystem action
