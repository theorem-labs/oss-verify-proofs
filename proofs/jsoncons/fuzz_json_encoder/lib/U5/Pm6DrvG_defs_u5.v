(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6MainEntry_u5 Pm6LibStdioCall_u5.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Drv_defs_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition STOPS_L : list Z := (0x3a1f8 :: STOPS)%Z.
Definition runL (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_L scr ss [].
(* [comment removed for export] *)
Definition STOPS_Q : list Z := [0xad914; 0xb2bb8; 0xaf8f8; 0xaf7b8; 0x3a610]%Z.
Definition runQ (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_Q scr ss [].
Definition no_sc : stdio_res := SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [].
Definition the_sc (o : option stdio_res) : stdio_res := match o with Some r => r | None => no_sc end.

(* [comment removed for export] *)
Definition kn_blk2 (v : nat) : list kentry := [KRange (EVar v) 4096 (2 ^ 47); KAlign (EVar v) 16]%Z.
(* [comment removed for export] *)
Definition keep_rd (kn : list kentry) : list kentry := kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.

(* [comment removed for export] *)
Definition below_frame (K : kentry) : bool :=
  match K with KWord (SA (EVar 0) off) _ _ => (off <? -128)%Z | _ => false end.
Definition knLP6 : list kentry := Eval vm_compute in List.filter (fun K => negb (below_frame K)) keepB.
Definition knLP : list kentry := kn_blk 48 65536 ++ knLP6.
(* [comment removed for export] *)
Definition cellR : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x3a258).
Definition cellC : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x3a26c).
Definition knRD : list kentry := cellR :: knLP.

(* [comment removed for export] *)
Definition srLP : list expr :=
  [ELit 0; EVar 7; EAlu ALU_ADD (EVar 0) (ELit (-128)); ELit 67584; ELit 905232; EVar 11; EVar 12; EVar 13;
   ELit 2; EVar 48; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 2; EVar 70; ELit 3; EVar 38; ELit 832905; EVar 48; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 34; EVar 35; EVar 36; EVar 37]%Z.
(* [comment removed for export] *)
Definition srRD : list expr :=
  [ELit 0; ELit 798580; EAlu ALU_ADD (EVar 0) (ELit (-144)); ELit 67584; ELit 905232; EVar 11; EVar 12; EVar 13;
   ELit 2; EVar 48; ELit 3; ELit 832905; EVar 71; ELit 0; ELit 0; ELit 0; ELit 0; ELit 63;
   EVar 2; EVar 70; ELit 3; EVar 38; ELit 832905; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 34; EVar 35; EVar 36; EVar 37]%Z.

(* [comment removed for export] *)
Definition rC0L := Eval vm_compute in runL scr0 (SS 0x3a1c4 srC0 [] knC0 70).
Definition srC0L : list expr := Eval vm_compute in s_regs (fst (fst rC0L)).

(* [comment removed for export] *)
Definition knLPp : list kentry := KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLP.
(* [comment removed for export] *)
Definition rPa := Eval vm_compute in runL (SCR [false; false] [] []) (SS 0x3a1f8 srLP [] knLPp 71).
Definition srPa : list expr := Eval vm_compute in s_regs (fst (fst rPa)).
Definition knRDp : list kentry := Eval vm_compute in kn_after rPa knLPp.
(* [comment removed for export] *)
Definition rPb := Eval vm_compute in runL (SCR [false; true] [] []) (SS 0x3a1f8 srLP [] knLPp 71).
Definition srPb : list expr := Eval vm_compute in s_regs (fst (fst rPb)).
(* [comment removed for export] *)
Definition want_x : expr := Eval vm_compute in nth 12 srPb (ELit 0).

(* [comment removed for export] *)
Definition srRe0 : list expr := sr_upd srRD (ridx 10) (EVar 72).
Definition knRe0 : list kentry := KRange (EVar 72) 1 65536 :: knRD.
Definition rRe_tk := Eval vm_compute in runL scr0 (SS 0xbeff4 srRe0 [] knRe0 73).
Definition srRe_tk : list expr := Eval vm_compute in s_regs (fst (fst rRe_tk)).
Definition knRe_tk : list kentry := Eval vm_compute in kn_after rRe_tk knRe0.
(* [comment removed for export] *)
Definition srRm0 : list expr := Eval vm_compute in sr_after_call_j srRe_tk (map ridx callee_kept) 73.
Definition rRm := Eval vm_compute in runL scr0 (SS 0x3a1f0 srRm0 [] knRe_tk 105).
Definition srRm : list expr := Eval vm_compute in s_regs (fst (fst rRm)).
(* [comment removed for export] *)
Definition len_x : expr := Eval vm_compute in nth 19 srRm (ELit 0).
(* [comment removed for export] *)
Definition srRf0 : list expr := sr_upd srRD (ridx 10) (ELit 0).
Definition rRe_ft := Eval vm_compute in runL scr0 (SS 0xbeff4 srRf0 [] knRD 73).
Definition srRe_ft : list expr := Eval vm_compute in s_regs (fst (fst rRe_ft)).
Definition knRe_ft : list kentry := Eval vm_compute in kn_after rRe_ft knRD.

(* [comment removed for export] *)
Definition srGL : list expr := Eval vm_compute in sr_upd srRe_ft (ridx 10) (ELit 0).
Definition knGbase : list kentry := cellC :: knLP.
Definition knG (lo hi : Z) : list kentry := KRange (EVar 70) lo hi :: knGbase.

(* [comment removed for export] *)
Definition knLPg : list kentry := KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLP.
Definition rGa := Eval vm_compute in runL (SCR [true] [] []) (SS 0x3a1f8 srLP [] knLPg 71).
Definition srGa : list expr := Eval vm_compute in s_regs (fst (fst rGa)).
Definition knGa : list kentry := Eval vm_compute in kn_after rGa knLPg.
(* [comment removed for export] *)
Definition cap2_x : expr := Eval vm_compute in nth 10 srGa (ELit 0).
(* [comment removed for export] *)
Definition srGb0 : list expr := Eval vm_compute in sr_after_call_j srGa (map ridx c_kept) 71.
Definition knGb0 : list kentry := Eval vm_compute in kn_blk2 81 ++ keep_alloc MSO [(48%nat, 65536%Z)] [] knGa.
Definition rGb := Eval vm_compute in runL scr0 (SS 0x3a218 srGb0 [] knGb0 103).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
(* [comment removed for export] *)
Definition srGc0 : list expr := Eval vm_compute in sr_after_call_j srGb (map ridx callee_kept) 103.
Definition knGc0 : list kentry := Eval vm_compute in keep_rd knGb0.
Definition rGc := Eval vm_compute in runL scr0 (SS 0x3a234 srGc0 [] knGc0 135).
Definition srGc : list expr := Eval vm_compute in s_regs (fst (fst rGc)).
(* [comment removed for export] *)
Definition srGd0 : list expr := Eval vm_compute in sr_after_call_j srGc (map ridx c_kept) 135.
Definition knGd0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knGc0.
Definition rGd := Eval vm_compute in runL scr0 (SS 0x3a23c srGd0 [] knGd0 167).
Definition srGd : list expr := Eval vm_compute in s_regs (fst (fst rGd)).
Definition knGd : list kentry := Eval vm_compute in kn_after rGd knGd0.

(* [comment removed for export] *)
Definition knLPr : list kentry := KRange (EVar 70) 67108864 67108864 :: KRange (EVar 38) 67108864 67108864 :: knLP.
(* [comment removed for export] *)
Definition scr_refuse : scripts := SCR [false; false; true; true] [] [].
Definition rRa := Eval vm_compute in runQ scr_refuse (SS 0x3a1f8 srLP [] knLPr 71).
Definition srRa : list expr := Eval vm_compute in s_regs (fst (fst rRa)).
Definition knRa : list kentry := Eval vm_compute in kn_after rRa knLPr.
Definition scR : stdio_res := Eval vm_compute in the_sc (stdio_call 71 srRa knRa).
Definition srRb0 : list expr := Eval vm_compute in sc_sr scR.
Definition knRb0 : list kentry := Eval vm_compute in sc_kn scR.
Definition rRb := Eval vm_compute in runQ scr0 (SS (sc_ret scR) srRb0 [] knRb0 103).
Definition srRb : list expr := Eval vm_compute in s_regs (fst (fst rRb)).
Definition knRb : list kentry := Eval vm_compute in kn_after rRb knRb0.

(* [comment removed for export] *)
Definition summG (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
Definition kdiff (a b : list kentry) := List.filter (fun K => negb (existsb (kentry_eqb K) b)) a.
Lemma loop_itinerary_ok :
  summG rC0L = (0xbeff0%Z, [], 70%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x3a258%Z)]) /\ kn_after rC0L knC0 = cellR :: knC0
  /\ kdiff knLP knC0 = [] /\ kn_vars_lt 6 knLP6 = true
  /\ (nth 21 srC0L (ELit 0), nth 9 srC0L (ELit 0), nth 19 srC0L (ELit 0), nth 12 srC0L (ELit 0), nth 11 srC0L (ELit 0), nth 10 srC0L (ELit 0), nth 17 srC0L (ELit 0))
     = (ELit 65536, EVar 48, ELit 0, ELit 65536, ELit 832905, ELit 3, ELit 63)
  /\ summG rPa = (0xbeff0%Z, [SCBr false BC_LTU want_x (ELit 65536); SCBr false BC_EQ (EVar 70) (EVar 38)], 71%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x3a258%Z)])
  /\ summG rPb = (0xbeff0%Z, [SCBr true BC_LTU want_x (ELit 65536); SCBr false BC_EQ (EVar 70) (EVar 38)], 71%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x3a258%Z)])
  /\ kn_after rPb knLPp = knRDp /\ knRDp = cellR :: knLPp
  /\ srPb = sr_upd srPa (ridx 12) want_x /\ srPa = sr_upd (sr_upd srRD (ridx 12) (ELit 65536)) (ridx 23) (EVar 48)
  /\ want_x = EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit (-1)) (EVar 70))
  /\ summG rRe_tk = (0xbe048%Z, [], 73%nat, []) /\ kn_after rRe_tk knRe0 = knRe0 /\ keep_rd knRe0 = knRe0
  /\ (nth 10 srRe_tk (ELit 0), nth 11 srRe_tk (ELit 0), nth 12 srRe_tk (ELit 0), nth 1 srRe_tk (ELit 0), nth 2 srRe_tk (ELit 0))
     = (EAlu ALU_ADD (EVar 48) (EVar 70), ELit 832905, EVar 72, ELit 0x3a1f0%Z, EAlu ALU_ADD (EVar 0) (ELit (-128)))
  /\ summG rRm = (0x3a1f8%Z, [], 105%nat, []) /\ len_x = EAlu ALU_ADD (EVar 70) (EVar 72)
  /\ (nth 9 srRm (ELit 0), nth 23 srRm (ELit 0), nth 21 srRm (ELit 0), nth 18 srRm (ELit 0), nth 2 srRm (ELit 0))
     = (EVar 48, EVar 48, EVar 38, EVar 2, EAlu ALU_ADD (EVar 0) (ELit (-128)))
  /\ summG rRe_ft = (0xbeff0%Z, [], 73%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x3a26c%Z)]) /\ knRe_ft = cellC :: knLP
  /\ (nth 10 srRe_ft (ELit 0), nth 17 srRe_ft (ELit 0)) = (ELit 3, ELit 57) /\ sr_vars_lt 71 srGL = true
  /\ summG rGa = (0xaf8f8%Z, [SCBr true BC_EQ (EVar 70) (EVar 38)], 71%nat, [])
  /\ kn_after rGa knLPg = knLPg /\ nth 10 srGa (ELit 0) = cap2_x /\ nth 21 srGa (ELit 0) = cap2_x /\ cap2_x = EMd M_MUL (ELit 2) (EVar 70)
  /\ nth 1 srGa (ELit 0) = ELit 0x3a218%Z /\ nth 2 srGa (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit MSO)
  /\ summG rGb = (0xbe048%Z, [], 103%nat, []) /\ kn_after rGb knGb0 = knGb0
  /\ (nth 10 srGb (ELit 0), nth 11 srGb (ELit 0), nth 12 srGb (ELit 0), nth 1 srGb (ELit 0)) = (EVar 81, EVar 48, EVar 70, ELit 0x3a234%Z)
  /\ kdiff knGb0 knGc0 = []
  /\ summG rGc = (0xaf7b8%Z, [], 135%nat, []) /\ kn_after rGc knGc0 = knGc0 /\ nth 10 srGc (ELit 0) = EVar 48
  /\ nth 1 srGc (ELit 0) = ELit 0x3a23c%Z /\ nth 2 srGc (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit MSO)
  /\ summG rGd = (0xbeff0%Z, [], 167%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x3a258%Z)])
  /\ (nth 10 srGd (ELit 0), nth 11 srGd (ELit 0), nth 12 srGd (ELit 0), nth 17 srGd (ELit 0), nth 9 srGd (ELit 0), nth 21 srGd (ELit 0), nth 19 srGd (ELit 0))
     = (ELit 3, ELit 832905, ELit 65536, ELit 63, EVar 81, cap2_x, EVar 70)
  /\ (s_pc (fst (fst rRa)), s_next (fst (fst rRa))) = (0xb2bb8%Z, 71%nat)
  /\ stdio_call 71 srRa knRa = Some scR /\ (sc_ret scR, sc_f scR, sc_fd scR, sc_s scR, sc_l scR) = (0xb3864%Z, 0xcb338%Z, 2%Z, ELit 0, ELit 0)
  /\ (sc_wb scR, sc_wp scR, sc_sp scR) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), EAlu ALU_ADD (EVar 0) (ELit (-576)))
  /\ summG rRb = (0xad914%Z, [], 103%nat, s_log (fst (fst rRb))) /\ nth 10 srRb (ELit 0) = ELit 2.
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.
