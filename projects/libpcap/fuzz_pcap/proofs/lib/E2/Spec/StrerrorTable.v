(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List String.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* [comment removed for export] *)
Definition STRERROR_N : Z := 132.

(* [comment removed for export] *)
Definition strerror_table : list (Z * string) := [
  (0, "No error information");
  (84, "Illegal byte sequence");
  (33, "Domain error");
  (34, "Result not representable");
  (25, "Not a tty");
  (13, "Permission denied");
  (1, "Operation not permitted");
  (2, "No such file or directory");
  (3, "No such process");
  (17, "File exists");
  (75, "Value too large for data type");
  (28, "No space left on device");
  (12, "Out of memory");
  (16, "Resource busy");
  (4, "Interrupted system call");
  (11, "Resource temporarily unavailable");
  (29, "Invalid seek");
  (18, "Cross-device link");
  (30, "Read-only file system");
  (39, "Directory not empty");
  (104, "Connection reset by peer");
  (110, "Operation timed out");
  (111, "Connection refused");
  (112, "Host is down");
  (113, "Host is unreachable");
  (98, "Address in use");
  (32, "Broken pipe");
  (5, "I/O error");
  (6, "No such device or address");
  (15, "Block device required");
  (19, "No such device");
  (20, "Not a directory");
  (21, "Is a directory");
  (26, "Text file busy");
  (8, "Exec format error");
  (22, "Invalid argument");
  (7, "Argument list too long");
  (40, "Symbolic link loop");
  (36, "Filename too long");
  (23, "Too many open files in system");
  (24, "No file descriptors available");
  (9, "Bad file descriptor");
  (10, "No child process");
  (14, "Bad address");
  (27, "File too large");
  (31, "Too many links");
  (37, "No locks available");
  (35, "Resource deadlock would occur");
  (131, "State not recoverable");
  (130, "Previous owner died");
  (125, "Operation canceled");
  (38, "Function not implemented");
  (42, "No message of desired type");
  (43, "Identifier removed");
  (60, "Device not a stream");
  (61, "No data available");
  (62, "Device timeout");
  (63, "Out of streams resources");
  (67, "Link has been severed");
  (71, "Protocol error");
  (74, "Bad message");
  (77, "File descriptor in bad state");
  (88, "Not a socket");
  (89, "Destination address required");
  (90, "Message too large");
  (91, "Protocol wrong type for socket");
  (92, "Protocol not available");
  (93, "Protocol not supported");
  (94, "Socket type not supported");
  (95, "Not supported");
  (96, "Protocol family not supported");
  (97, "Address family not supported by protocol");
  (99, "Address not available");
  (100, "Network is down");
  (101, "Network unreachable");
  (102, "Connection reset by network");
  (103, "Connection aborted");
  (105, "No buffer space available");
  (106, "Socket is connected");
  (107, "Socket not connected");
  (108, "Cannot send after socket shutdown");
  (114, "Operation already in progress");
  (115, "Operation in progress");
  (116, "Stale file handle");
  (117, "Data consistency error");
  (119, "Resource not available");
  (121, "Remote I/O error");
  (122, "Quota exceeded");
  (123, "No medium found");
  (124, "Wrong medium type");
  (72, "Multihop attempted");
  (126, "Required key not available");
  (127, "Key has expired");
  (128, "Key has been revoked");
  (129, "Key was rejected by service")
].

Definition strerror_default : string := "No error information".
