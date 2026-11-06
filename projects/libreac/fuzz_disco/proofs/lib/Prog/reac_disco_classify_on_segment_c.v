From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c classify_core_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_DISCO_CLASSIFY_ON_SEGMENT : Z := 0x15404.

Definition reac_disco_classify_on_segment_contract : Prop := classify_core_spec REAC_DISCO_CLASSIFY_ON_SEGMENT.
