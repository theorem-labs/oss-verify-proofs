(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import RefExitBase RefStdioDefs AsStdioCall AsPrintfFirst.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsExit Require Import FeDefs AsUnreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

Definition AEXIT : Z := 0x524f4c.
Definition AEXIT_LR : Z := 0x524f6c.      (* [comment removed for export] *)
Definition AEXIT_CAS_RET : Z := 0x524f78. (* [comment removed for export] *)
Definition AEXIT_ECALL : Z := 0x524d20.
Definition ASTDIO_WRITE : Z := 0x52aa6c.
Definition AX_FR : Z := 1024.
Definition XFUEL : nat := 20000.
Definition XSTOPS : list Z := [FE_ENTRY; ASTDIO_WRITE]%Z.
Definition NV : nat := 41.

Definition x_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0 | 4 => ELit 0xbae650%Z | 10 => EVar 2
                          | _ => EVar (8 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition ax_lit_cells : list (Z * nat * Z) :=
  [(0xbce8c0, 4%nat, 0);          (* [comment removed for export] *)
   (0xbce8e3, 1%nat, 0);          (* [comment removed for export] *)
   (0xbce6a4, 4%nat, 0);          (* [comment removed for export] *)
   (0xbce6b0, 8%nat, 0xbce6b8);   (* [comment removed for export] *)
   (0xbce6b8, 8%nat, 0);          (* [comment removed for export] *)
   (0xbce6c0, 8%nat, 0x524ef8);   (* [comment removed for export] *)
   (0xbce7c0, 8%nat, 0x1e37f4);   (* [comment removed for export] *)
   (0x709160, 1%nat, 0);          (* [comment removed for export] *)
   (0x673c50, 1%nat, 0);          (* [comment removed for export] *)
   (0x5b16a0, 8%nat, 0x5b16a0);   (* [comment removed for export] *)
   (0x673c00, 8%nat, 1);          (* [comment removed for export] *)
   (0xba9e00, 1%nat, 0);          (* [comment removed for export] *)
   (0xbced48, 8%nat, 0);          (* [comment removed for export] *)
   (0x5b48d4, 4%nat, 0xffffffff); (* [comment removed for export] *)
   (0x5b4ab4, 4%nat, 0xffffffff)  (* [comment removed for export] *)]%Z
  ++ FE_CELLS.                    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ax_atexit_cells (ax2 : bool) : list (Z * nat * Z) :=
  if ax2 then [(0xbce6a8, 4%nat, 2); (0xbce6c8, 8%nat, 0x524ef8); (0xbce7c8, 8%nat, 0x1f422c); (0xba9914, 1%nat, 0)]%Z
  else [(0xbce6a8, 4%nat, 1)]%Z.

(* [comment removed for export] *)
Definition ax_flush_cells : list (Z * nat * Z) :=
  [(0x5b4a60, 8%nat, 0xbcf168); (0x5b4a70, 8%nat, 0x52aa6c); (0x5b4a80, 8%nat, 0xbcf168); (0x5b4a88, 8%nat, 1024); (0x5b4aa0, 4%nat, 1)]%Z.

Definition ax_kn (ax2 binz fl : bool) : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI; KWr (SA (EVar 0) (-1024)) 1024; KRange (EVar 1) 1 2147483647;
   KImg 0x10000 0x19a000; KImg 0x19a000 0x538000; KImg 0x538000 0x5b1000; KImg 0x5b4930 0x5b4a28; KImg 0x5b4b10 0x5b4b28; KImg 0x5b4b30 0x673c00;
   KWord (SA (ELit 0) 0xbae5a8) 4 (EVar 1); KWord (SA (ELit 0) 0xbce690) 8 (EVar 3);
   KWord (SA (ELit 0) 0x5b4870) 8 (EVar 5); KWord (SA (ELit 0) 0x5b4880) 8 (EVar 5);
   KWord (SA (ELit 0) 0x5b4850) 8 (EVar 6); KWord (SA (ELit 0) 0x5b4858) 8 (EVar 6);
   KWord (SA (ELit 0) 0x5b4a30) 8 (EVar 7); KWord (SA (ELit 0) 0x5b4a38) 8 (EVar 7);
   KWr (SA (ELit 0) 0xbce6a0) 24; KWr (SA (ELit 0) 0xbce8c0) 4; KWr (SA (ELit 0) 0x673c50) 1; KWr (SA (ELit 0) 0x673c00) 8;
   KWr (SA (ELit 0) 0x7fffa000) 0x178000; KWr (SA (ELit 0) 0x5b4a28) 232]%Z
  ++ (if binz then [KWord (SA (ELit 0) 0xba9de0) 1 (EVar 40); KRange (EVar 40) 1 255]%Z else [KWord (SA (ELit 0) 0xba9de0) 1 (ELit 0)]%Z)
  ++ (if fl then [KWord (SA (ELit 0) 0x5b4a50) 8 (EVar 4); KRange (EVar 4) 0xbcf169 0xbcf568]%Z ++ kn_cells ax_flush_cells
      else [KWord (SA (ELit 0) 0x5b4a50) 8 (EVar 4); KWord (SA (ELit 0) 0x5b4a60) 8 (EVar 4)]%Z)
  ++ kn_cells (ax_atexit_cells ax2) ++ kn_cells ax_lit_cells.

Definition scr0 : scripts := SCR [] [] [].

(* [comment removed for export] *)
Definition uc_of (o : option unreg_res) : unreg_res := match o with Some r => r | None => UCR [] [] end.
Definition sc_of (o : option stdio_res) : stdio_res :=
  match o with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX11c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn false false false) NV) []).
Definition srX11c := Eval vm_compute in (s_regs (fst (fst rX11c))).
Definition cX11c := Eval vm_compute in (carry (s_log (fst (fst rX11c))) (ax_kn false false false) []).
Definition knX11c := Eval vm_compute in (fst (fst cX11c)).
(* [comment removed for export] *)
Definition srX2i1c := Eval vm_compute in (sr_upd (sr_upd srX11c (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2i1c := Eval vm_compute in (carry [SE (SA (ELit 0) 0xbce8c0) 4 (sr_get srX11c 12)] knX11c []).
Definition knX2i1c := Eval vm_compute in (fst (fst cX2i1c)).
(* [comment removed for export] *)
Definition rX21c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT_CAS_RET srX2i1c [] knX2i1c NV) []).
Definition srX21c := Eval vm_compute in (s_regs (fst (fst rX21c))).
Definition cX21c := Eval vm_compute in (carry (s_log (fst (fst rX21c))) knX2i1c []).
Definition knX21c := Eval vm_compute in (fst (fst cX21c)).
(* [comment removed for export] *)
Definition uX1c := Eval vm_compute in (uc_of (unreg_call NV srX21c knX21c)).
(* [comment removed for export] *)
Definition rX31c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS FE_RET (uc_sr uX1c) [] (uc_kn uX1c) 73) []).
Definition srX31c := Eval vm_compute in (s_regs (fst (fst rX31c))).
Definition cX31c := Eval vm_compute in (carry (s_log (fst (fst rX31c))) (uc_kn uX1c) []).
Definition knX31c := Eval vm_compute in (fst (fst cX31c)).
Lemma x_itinerary_1c :
  s_pc (fst (fst rX11c)) = AEXIT_LR /\ snd (fst rX11c) = [] /\ snd (fst cX11c) = []
  /\ snd (fst cX2i1c) = [] /\ kread RSEGS knX11c (ELit 0) 0xbce8c0 4 = Some (ELit 0)
  /\ s_pc (fst (fst rX21c)) = FE_ENTRY /\ snd (fst rX21c) = [] /\ snd (fst cX21c) = []
  /\ unreg_call NV srX21c knX21c = Some uX1c
  /\ s_pc (fst (fst rX31c)) = AEXIT_ECALL /\ snd (fst rX31c) = [] /\ snd (fst cX31c) = [].
Proof. repeat apply conj; lazymatch goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX12zc := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true false false) NV) []).
Definition srX12zc := Eval vm_compute in (s_regs (fst (fst rX12zc))).
Definition cX12zc := Eval vm_compute in (carry (s_log (fst (fst rX12zc))) (ax_kn true false false) []).
Definition knX12zc := Eval vm_compute in (fst (fst cX12zc)).
(* [comment removed for export] *)
Definition srX2i2zc := Eval vm_compute in (sr_upd (sr_upd srX12zc (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2i2zc := Eval vm_compute in (carry [SE (SA (ELit 0) 0xbce8c0) 4 (sr_get srX12zc 12)] knX12zc []).
Definition knX2i2zc := Eval vm_compute in (fst (fst cX2i2zc)).
(* [comment removed for export] *)
Definition rX22zc := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT_CAS_RET srX2i2zc [] knX2i2zc NV) []).
Definition srX22zc := Eval vm_compute in (s_regs (fst (fst rX22zc))).
Definition cX22zc := Eval vm_compute in (carry (s_log (fst (fst rX22zc))) knX2i2zc []).
Definition knX22zc := Eval vm_compute in (fst (fst cX22zc)).
(* [comment removed for export] *)
Definition uX2zc := Eval vm_compute in (uc_of (unreg_call NV srX22zc knX22zc)).
(* [comment removed for export] *)
Definition rX32zc := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS FE_RET (uc_sr uX2zc) [] (uc_kn uX2zc) 73) []).
Definition srX32zc := Eval vm_compute in (s_regs (fst (fst rX32zc))).
Definition cX32zc := Eval vm_compute in (carry (s_log (fst (fst rX32zc))) (uc_kn uX2zc) []).
Definition knX32zc := Eval vm_compute in (fst (fst cX32zc)).
Lemma x_itinerary_2zc :
  s_pc (fst (fst rX12zc)) = AEXIT_LR /\ snd (fst rX12zc) = [] /\ snd (fst cX12zc) = []
  /\ snd (fst cX2i2zc) = [] /\ kread RSEGS knX12zc (ELit 0) 0xbce8c0 4 = Some (ELit 0)
  /\ s_pc (fst (fst rX22zc)) = FE_ENTRY /\ snd (fst rX22zc) = [] /\ snd (fst cX22zc) = []
  /\ unreg_call NV srX22zc knX22zc = Some uX2zc
  /\ s_pc (fst (fst rX32zc)) = AEXIT_ECALL /\ snd (fst rX32zc) = [] /\ snd (fst cX32zc) = [].
Proof. repeat apply conj; lazymatch goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX12zf := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true false true) NV) []).
Definition srX12zf := Eval vm_compute in (s_regs (fst (fst rX12zf))).
Definition cX12zf := Eval vm_compute in (carry (s_log (fst (fst rX12zf))) (ax_kn true false true) []).
Definition knX12zf := Eval vm_compute in (fst (fst cX12zf)).
(* [comment removed for export] *)
Definition srX2i2zf := Eval vm_compute in (sr_upd (sr_upd srX12zf (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2i2zf := Eval vm_compute in (carry [SE (SA (ELit 0) 0xbce8c0) 4 (sr_get srX12zf 12)] knX12zf []).
Definition knX2i2zf := Eval vm_compute in (fst (fst cX2i2zf)).
(* [comment removed for export] *)
Definition rX22zf := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT_CAS_RET srX2i2zf [] knX2i2zf NV) []).
Definition srX22zf := Eval vm_compute in (s_regs (fst (fst rX22zf))).
Definition cX22zf := Eval vm_compute in (carry (s_log (fst (fst rX22zf))) knX2i2zf []).
Definition knX22zf := Eval vm_compute in (fst (fst cX22zf)).
(* [comment removed for export] *)
Definition uX2zf := Eval vm_compute in (uc_of (unreg_call NV srX22zf knX22zf)).
(* [comment removed for export] *)
Definition rX32zf := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS FE_RET (uc_sr uX2zf) [] (uc_kn uX2zf) 73) []).
Definition srX32zf := Eval vm_compute in (s_regs (fst (fst rX32zf))).
Definition cX32zf := Eval vm_compute in (carry (s_log (fst (fst rX32zf))) (uc_kn uX2zf) []).
Definition knX32zf := Eval vm_compute in (fst (fst cX32zf)).
(* [comment removed for export] *)
Definition scX2zf : stdio_res := Eval vm_compute in (sc_of (stdio_call 73 srX32zf knX32zf)).
Definition rX42zf := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS (sc_ret scX2zf) (sc_sr scX2zf) [] (sc_kn scX2zf) 105) []).
Definition srX42zf := Eval vm_compute in (s_regs (fst (fst rX42zf))).
Definition cX42zf := Eval vm_compute in (carry (s_log (fst (fst rX42zf))) (sc_kn scX2zf) []).
Lemma x_itinerary_2zf :
  s_pc (fst (fst rX12zf)) = AEXIT_LR /\ snd (fst rX12zf) = [] /\ snd (fst cX12zf) = []
  /\ snd (fst cX2i2zf) = [] /\ kread RSEGS knX12zf (ELit 0) 0xbce8c0 4 = Some (ELit 0)
  /\ s_pc (fst (fst rX22zf)) = FE_ENTRY /\ snd (fst rX22zf) = [] /\ snd (fst cX22zf) = []
  /\ unreg_call NV srX22zf knX22zf = Some uX2zf
  /\ s_pc (fst (fst rX32zf)) = ASTDIO_WRITE /\ snd (fst rX32zf) = [] /\ snd (fst cX32zf) = []
  /\ stdio_call 73 srX32zf knX32zf = Some scX2zf
  /\ s_pc (fst (fst rX42zf)) = AEXIT_ECALL /\ snd (fst rX42zf) = [] /\ snd (fst cX42zf) = [].
Proof. repeat apply conj; lazymatch goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX12nc := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true true false) NV) []).
Definition srX12nc := Eval vm_compute in (s_regs (fst (fst rX12nc))).
Definition cX12nc := Eval vm_compute in (carry (s_log (fst (fst rX12nc))) (ax_kn true true false) []).
Definition knX12nc := Eval vm_compute in (fst (fst cX12nc)).
(* [comment removed for export] *)
Definition srX2i2nc := Eval vm_compute in (sr_upd (sr_upd srX12nc (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2i2nc := Eval vm_compute in (carry [SE (SA (ELit 0) 0xbce8c0) 4 (sr_get srX12nc 12)] knX12nc []).
Definition knX2i2nc := Eval vm_compute in (fst (fst cX2i2nc)).
(* [comment removed for export] *)
Definition rX22nc := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT_CAS_RET srX2i2nc [] knX2i2nc NV) []).
Definition srX22nc := Eval vm_compute in (s_regs (fst (fst rX22nc))).
Definition cX22nc := Eval vm_compute in (carry (s_log (fst (fst rX22nc))) knX2i2nc []).
Definition knX22nc := Eval vm_compute in (fst (fst cX22nc)).
(* [comment removed for export] *)
Definition uX2nc := Eval vm_compute in (uc_of (unreg_call NV srX22nc knX22nc)).
(* [comment removed for export] *)
Definition rX32nc := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS FE_RET (uc_sr uX2nc) [] (uc_kn uX2nc) 73) []).
Definition srX32nc := Eval vm_compute in (s_regs (fst (fst rX32nc))).
Definition cX32nc := Eval vm_compute in (carry (s_log (fst (fst rX32nc))) (uc_kn uX2nc) []).
Definition knX32nc := Eval vm_compute in (fst (fst cX32nc)).
Lemma x_itinerary_2nc :
  s_pc (fst (fst rX12nc)) = AEXIT_LR /\ snd (fst rX12nc) = [] /\ snd (fst cX12nc) = []
  /\ snd (fst cX2i2nc) = [] /\ kread RSEGS knX12nc (ELit 0) 0xbce8c0 4 = Some (ELit 0)
  /\ s_pc (fst (fst rX22nc)) = FE_ENTRY /\ snd (fst rX22nc) = [] /\ snd (fst cX22nc) = []
  /\ unreg_call NV srX22nc knX22nc = Some uX2nc
  /\ s_pc (fst (fst rX32nc)) = AEXIT_ECALL /\ snd (fst rX32nc) = [] /\ snd (fst cX32nc) = [].
Proof. repeat apply conj; lazymatch goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX12nf := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true true true) NV) []).
Definition srX12nf := Eval vm_compute in (s_regs (fst (fst rX12nf))).
Definition cX12nf := Eval vm_compute in (carry (s_log (fst (fst rX12nf))) (ax_kn true true true) []).
Definition knX12nf := Eval vm_compute in (fst (fst cX12nf)).
(* [comment removed for export] *)
Definition srX2i2nf := Eval vm_compute in (sr_upd (sr_upd srX12nf (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2i2nf := Eval vm_compute in (carry [SE (SA (ELit 0) 0xbce8c0) 4 (sr_get srX12nf 12)] knX12nf []).
Definition knX2i2nf := Eval vm_compute in (fst (fst cX2i2nf)).
(* [comment removed for export] *)
Definition rX22nf := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT_CAS_RET srX2i2nf [] knX2i2nf NV) []).
Definition srX22nf := Eval vm_compute in (s_regs (fst (fst rX22nf))).
Definition cX22nf := Eval vm_compute in (carry (s_log (fst (fst rX22nf))) knX2i2nf []).
Definition knX22nf := Eval vm_compute in (fst (fst cX22nf)).
(* [comment removed for export] *)
Definition uX2nf := Eval vm_compute in (uc_of (unreg_call NV srX22nf knX22nf)).
(* [comment removed for export] *)
Definition rX32nf := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS FE_RET (uc_sr uX2nf) [] (uc_kn uX2nf) 73) []).
Definition srX32nf := Eval vm_compute in (s_regs (fst (fst rX32nf))).
Definition cX32nf := Eval vm_compute in (carry (s_log (fst (fst rX32nf))) (uc_kn uX2nf) []).
Definition knX32nf := Eval vm_compute in (fst (fst cX32nf)).
(* [comment removed for export] *)
Definition scX2nf : stdio_res := Eval vm_compute in (sc_of (stdio_call 73 srX32nf knX32nf)).
Definition rX42nf := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS (sc_ret scX2nf) (sc_sr scX2nf) [] (sc_kn scX2nf) 105) []).
Definition srX42nf := Eval vm_compute in (s_regs (fst (fst rX42nf))).
Definition cX42nf := Eval vm_compute in (carry (s_log (fst (fst rX42nf))) (sc_kn scX2nf) []).
Lemma x_itinerary_2nf :
  s_pc (fst (fst rX12nf)) = AEXIT_LR /\ snd (fst rX12nf) = [] /\ snd (fst cX12nf) = []
  /\ snd (fst cX2i2nf) = [] /\ kread RSEGS knX12nf (ELit 0) 0xbce8c0 4 = Some (ELit 0)
  /\ s_pc (fst (fst rX22nf)) = FE_ENTRY /\ snd (fst rX22nf) = [] /\ snd (fst cX22nf) = []
  /\ unreg_call NV srX22nf knX22nf = Some uX2nf
  /\ s_pc (fst (fst rX32nf)) = ASTDIO_WRITE /\ snd (fst rX32nf) = [] /\ snd (fst cX32nf) = []
  /\ stdio_call 73 srX32nf knX32nf = Some scX2nf
  /\ s_pc (fst (fst rX42nf)) = AEXIT_ECALL /\ snd (fst rX42nf) = [] /\ snd (fst cX42nf) = [].
Proof. repeat apply conj; lazymatch goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
