(* Image shim and address block of the musl half of the strcspn walk on plugin-hostd/fuzz_command's ASan+UBSan
   build. rsegs is the ASan+UBSan image, so the plain-model walks of lib/Prog/strcspn.v and lib/R_strchr.v copied
   into the RtSStrcspnM files run over it (the image-B twin of lib/A/Rt/RtSStrcspnMImg.v; the precedent is
   lib/A/Rt/RtNScanImg.v). Every address below is re-derived from fuzz_command.asan-ubsan (nm, objdump):
     strcspn   0x9ee10 (W, 0x118 bytes) = plain 0x20b6c + 0x7e2a4
     strchrnul 0x9ec10 (W, 0xe0 bytes)  = plain 0x20c84 + 0x7df8c
     0x9ee60 `jal 0x57674`  the memset trampoline (return address 0x9ee64)
     0x9eee4 `jal 0x9ec10`  strchrnul (return address 0x9eee8)
     0x9ecb0 `jal 0x4517c`  the strlen trampoline (return address 0x9ecb4)
     0x9ee2c/0x9ee30 `auipc a1,0x8; ld s2,-564(a1)`: the GOT word 0xa6bf8, which holds __stack_chk_guard 0x604158
     0x9ec4c/0x9ec50 and 0x9ec58/0x9ec5c: musl's word-loop constants at 0x10370 and 0x10358 *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition rsegs : list Segment := YB1v.tfibsegs.

Definition CM_STRCSPN : Z := 0x9ee10.
Definition CM_STRCHRNUL : Z := 0x9ec10.
Definition CM_MEMSET : Z := 0x57674.
Definition CM_MEMSET_RA : Z := 0x9ee64.
Definition CM_STRLEN : Z := 0x4517c.
Definition CM_STRLEN_RA : Z := 0x9ecb4.
Definition CM_GOT : Z := 0xa6bf8.
Definition CM_GUARD : Z := 0x604158.
Definition CM_CMAGIC_AT : Z := 0x10370.
Definition CM_HIGHS_AT : Z := 0x10358.
