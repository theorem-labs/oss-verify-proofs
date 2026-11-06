(* Image shim and address block of the musl half of the strcspn walk on plugin-hostd/fuzz_command's memory-checking
   (ASan) build. rsegs is the ASan image, so the plain-model walks of lib/Prog/strcspn.v and lib/R_strchr.v copied
   into the RtSStrcspnM files run over it (the precedent is lib/A/Rt/RtNScanImg.v). Every address below is
   re-derived from fuzz_command.asan (nm, objdump):
     strcspn   0x9f2b4 (W, 0x118 bytes) = plain 0x20b6c + 0x7e748
     strchrnul 0x9f0b4 (W, 0xe0 bytes)  = plain 0x20c84 + 0x7e430
     0x9f304 `jal 0x57628`  the memset trampoline (return address 0x9f308)
     0x9f388 `jal 0x9f0b4`  strchrnul (return address 0x9f38c)
     0x9f154 `jal 0x45130`  the strlen trampoline (return address 0x9f158)
     0x9f2d0/0x9f2d4 `auipc a1,0x8; ld s2,-568(a1)`: the GOT word 0xa7098, which holds __stack_chk_guard 0x6045d8
     0x9f0f0/0x9f0f4 and 0x9f0fc/0x9f100: musl's word-loop constants at 0x10370 and 0x10358 *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition rsegs : list Segment := AB1v.tfibsegs.

Definition CM_STRCSPN : Z := 0x9f2b4.
Definition CM_STRCHRNUL : Z := 0x9f0b4.
Definition CM_MEMSET : Z := 0x57628.
Definition CM_MEMSET_RA : Z := 0x9f308.
Definition CM_STRLEN : Z := 0x45130.
Definition CM_STRLEN_RA : Z := 0x9f158.
Definition CM_GOT : Z := 0xa7098.
Definition CM_GUARD : Z := 0x6045d8.
Definition CM_CMAGIC_AT : Z := 0x10370.
Definition CM_HIGHS_AT : Z := 0x10358.
