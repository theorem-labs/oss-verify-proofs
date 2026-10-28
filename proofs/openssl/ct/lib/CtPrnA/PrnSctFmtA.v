(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS Arr FP Frame Cells Step Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic ApErr PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit FX_lib F_pop_arg F_printf_iface I_vsnstmt GDesc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface W_akit W_bio_write Fr_BIO_vprintf Fr_BIO_printf W_bio_printf W_bio_printf2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition A_C1_A : Z := 0xa7aa0.      (* [comment removed for export] *)
Definition A_EMPTY_A : Z := 0xa7b00.   (* [comment removed for export] *)
Definition A_C2_A : Z := 0xa7b20.      (* [comment removed for export] *)
Definition A_C3_A : Z := 0xa7b60.      (* [comment removed for export] *)
Definition A_C4_A : Z := 0xa7b80.      (* [comment removed for export] *)
Definition A_C5_A : Z := 0xa7be0.      (* [comment removed for export] *)
Definition A_C6_A : Z := 0xa7c20.      (* [comment removed for export] *)
Definition A_C7_A : Z := 0xa7c60.      (* [comment removed for export] *)
Definition A_C8_A : Z := 0xa7ca0.      (* [comment removed for export] *)
Definition A_C9_A : Z := 0xa7cc0.      (* [comment removed for export] *)
Definition A_C10_A : Z := 0xa7d40.     (* [comment removed for export] *)
Definition A_C11_A : Z := 0xa7d00.     (* [comment removed for export] *)
Definition A_C18_A : Z := 0xa7d60.     (* [comment removed for export] *)

Lemma fmt_C1_roA : ro_bytes ctasegs A_C1_A (zb FMT_C1). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C2_roA : ro_bytes ctasegs A_C2_A (zb FMT_C2). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C3_roA : ro_bytes ctasegs A_C3_A (zb FMT_C3). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C4_roA : ro_bytes ctasegs A_C4_A (zb FMT_C4). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C5_roA : ro_bytes ctasegs A_C5_A (zb FMT_C5). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C6_roA : ro_bytes ctasegs A_C6_A (zb FMT_C6). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C7_roA : ro_bytes ctasegs A_C7_A (zb FMT_C7). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C8_roA : ro_bytes ctasegs A_C8_A (zb FMT_C8). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C9_roA : ro_bytes ctasegs A_C9_A (zb FMT_C9). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C10_roA : ro_bytes ctasegs A_C10_A (zb FMT_C10). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C11_roA : ro_bytes ctasegs A_C11_A (zb FMT_C11). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_C18_roA : ro_bytes ctasegs A_C18_A (zb FMT_C18). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma empty_lit_roA : ro_bytes ctasegs A_EMPTY_A (zb [] ++ Z_to_bv 8 0 :: zb [0; 0; 0; 0; 0; 0; 0]). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma vfmtA_of_pieces : forall A fmt args ps r (g : Z * Z * Z),
  ro_bytes ctasegs A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1x_ok fmt = true ->
  gd_memb g = true -> gd_beg g <= A -> A + zlength fmt <= gd_beg g + gd_size g -> 0x10000 <= A -> A + zlength fmt <= STATIC_SPLIT ->
  printf_piecesx fmt args = Some (ps, r) -> r <= 80 -> fp_callsx (length fmt) fmt args = [] -> pcomx_ok fmt args = true -> fmtz_ok fmt = true ->
  vfmtA_ok A fmt args (concat ps).
Proof.
  intros A fmt args ps r g RO FB P1 GM G1 G2 A1 A2 P Hr FP PC FZ. pose proof (printf_piecesx_count _ _ _ _ P) as L.
  split; [exact RO|]. split; [exact FB|]. split; [exact A1|]. split; [exact A2|].
  split. { intros AR' Σ' OW' LB' m' H. eapply (af_lib_acc_lit _ (@ar_AF AR') Σ' m' g); [exact (@AH_art AR' _ _ _ _ H)| exact GM| exact G1| exact G2]. }
  split; [exact P1|].
  split. { rewrite L. apply (printf_modelx_sn _ _ _ _ P). lazymatch goal with |- _ <= ?cap => change (zlength (concat ps) <= cap) end.
           rewrite L. unfold OssFuzzTheorems.Proofs.openssl.ct.lib.P.F_printf_iface.SN_CAP. clear - Hr. lia. }
  split; [exact FP|]. split; [exact PC| exact FZ].
Qed.

Local Ltac vf RO FB P1 g PC n :=
  eapply (vfmtA_of_pieces _ _ _ _ _ g RO FB P1); [vm_compute; reflexivity| cbv -[Z.le Z.lt Z.add]; clear; lia| cbv -[Z.le Z.lt Z.add]; clear; lia| cbv -[Z.le Z.lt Z.add]; clear; lia
    | cbv -[Z.le Z.lt Z.add]; clear; lia| exact PC| clear; lia| apply fp_callsx_nog; repeat constructor| vm_compute; reflexivity| vm_compute; reflexivity].

(* [comment removed for export] *)
Definition O_C1 : list Z := [32; 32; 32; 32; 83; 105; 103; 110; 101; 100; 32; 67; 101; 114; 116; 105; 102; 105; 99; 97; 116; 101; 32; 84; 105; 109; 101; 115; 116; 97; 109; 112; 58].
Definition O_C2 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 86; 101; 114; 115; 105; 111; 110; 32; 32; 32; 58; 32].
Definition O_C3 : list Z := [117; 110; 107; 110; 111; 119; 110; 10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32].
Definition O_C4 : list Z := [118; 49; 32; 40; 48; 120; 48; 41].
Definition O_C5 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 76; 111; 103; 32; 73; 68; 32; 32; 32; 32; 58; 32].
Definition O_C6 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 84; 105; 109; 101; 115; 116; 97; 109; 112; 32; 58; 32].
Definition O_C7 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 69; 120; 116; 101; 110; 115; 105; 111; 110; 115; 58; 32].
Definition O_C8 : list Z := [110; 111; 110; 101].
Definition O_C9 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 83; 105; 103; 110; 97; 116; 117; 114; 101; 32; 58; 32].
Definition O_C11 : list Z := [10; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32].

Lemma vfmtA_C1 : vfmtA_ok A_C1_A FMT_C1 [PA_i 4; PA_s []] O_C1.
Proof. replace O_C1 with (concat [[]; [32; 32; 32; 32]; []; []; [83; 105; 103; 110; 101; 100; 32; 67; 101; 114; 116; 105; 102; 105; 99; 97; 116; 101; 32; 84; 105; 109; 101; 115; 116; 97; 109; 112; 58]]) by reflexivity.
  vf fmt_C1_roA fmt_bytes_C1 pass1x_ok_C1 (0xa7aa0, 33, 96) printf_piecesx_C1 33. Qed.
Lemma vfmtA_C2 : vfmtA_ok A_C2_A FMT_C2 [PA_i 8; PA_s []] O_C2.
Proof. replace O_C2 with (concat [[10]; []; zrepeat 32 8; []; []; [86; 101; 114; 115; 105; 111; 110; 32; 32; 32; 58; 32]]) by reflexivity.
  vf fmt_C2_roA fmt_bytes_C2 pass1x_ok_C2 (0xa7b20, 17, 64) printf_piecesx_C2 17. Qed.
Lemma vfmtA_C3 : vfmtA_ok A_C3_A FMT_C3 [PA_i 20; PA_s []] O_C3.
Proof. replace O_C3 with (concat [[117; 110; 107; 110; 111; 119; 110; 10]; []; zrepeat 32 20; []; []]) by reflexivity.
  vf fmt_C3_roA fmt_bytes_C3 pass1x_ok_C3 (0xa7b60, 12, 32) printf_piecesx_C3 12. Qed.
Lemma vfmtA_C4 : vfmtA_ok A_C4_A FMT_C4 [] O_C4.
Proof. replace O_C4 with (concat [[118; 49; 32; 40; 48; 120; 48; 41]]) by reflexivity.
  vf fmt_C4_roA fmt_bytes_C4 pass1x_ok_C4 (0xa7b80, 9, 32) printf_piecesx_C4 9. Qed.
Lemma vfmtA_C5 : vfmtA_ok A_C5_A FMT_C5 [PA_i 8; PA_s []] O_C5.
Proof. replace O_C5 with (concat [[10]; []; zrepeat 32 8; []; []; [76; 111; 103; 32; 73; 68; 32; 32; 32; 32; 58; 32]]) by reflexivity.
  vf fmt_C5_roA fmt_bytes_C5 pass1x_ok_C5 (0xa7be0, 17, 64) printf_piecesx_C5 17. Qed.
Lemma vfmtA_C6 : vfmtA_ok A_C6_A FMT_C6 [PA_i 8; PA_s []] O_C6.
Proof. replace O_C6 with (concat [[10]; []; zrepeat 32 8; []; []; [84; 105; 109; 101; 115; 116; 97; 109; 112; 32; 58; 32]]) by reflexivity.
  vf fmt_C6_roA fmt_bytes_C6 pass1x_ok_C6 (0xa7c20, 17, 64) printf_piecesx_C6 17. Qed.
Lemma vfmtA_C7 : vfmtA_ok A_C7_A FMT_C7 [PA_i 8; PA_s []] O_C7.
Proof. replace O_C7 with (concat [[10]; []; zrepeat 32 8; []; []; [69; 120; 116; 101; 110; 115; 105; 111; 110; 115; 58; 32]]) by reflexivity.
  vf fmt_C7_roA fmt_bytes_C7 pass1x_ok_C7 (0xa7c60, 17, 64) printf_piecesx_C7 17. Qed.
Lemma vfmtA_C8 : vfmtA_ok A_C8_A FMT_C8 [] O_C8.
Proof. replace O_C8 with (concat [[110; 111; 110; 101]]) by reflexivity.
  vf fmt_C8_roA fmt_bytes_C8 pass1x_ok_C8 (0xa7ca0, 5, 32) printf_piecesx_C8 5. Qed.
Lemma vfmtA_C9 : vfmtA_ok A_C9_A FMT_C9 [PA_i 8; PA_s []] O_C9.
Proof. replace O_C9 with (concat [[10]; []; zrepeat 32 8; []; []; [83; 105; 103; 110; 97; 116; 117; 114; 101; 32; 58; 32]]) by reflexivity.
  vf fmt_C9_roA fmt_bytes_C9 pass1x_ok_C9 (0xa7cc0, 17, 64) printf_piecesx_C9 17. Qed.
Lemma vfmtA_C11 : vfmtA_ok A_C11_A FMT_C11 [PA_i 8; PA_s []] O_C11.
Proof. replace O_C11 with (concat [[10]; []; zrepeat 32 8; []; []; zrepeat 32 12]) by reflexivity.
  vf fmt_C11_roA fmt_bytes_C11 pass1x_ok_C11 (0xa7d00, 17, 64) printf_piecesx_C11 17. Qed.
(* [comment removed for export] *)
Lemma vfmtA_C10 : forall s, zlength s <= 80 -> vfmtA_ok A_C10_A FMT_C10 [PA_s s] s.
Proof.
  intros s Hs. pose proof (zlength_nonneg'' s) as S0. destruct (printf_piecesx_C10 s ltac:(lia)) as (ps & P & CC). rewrite <- CC at 2.
  eapply (vfmtA_of_pieces _ _ _ _ _ (0xa7d40, 3, 32) fmt_C10_roA fmt_bytes_C10 pass1x_ok_C10); [vm_compute; reflexivity| cbv -[Z.le Z.lt Z.add]; clear; lia| cbv -[Z.le Z.lt Z.add]; clear; lia| cbv -[Z.le Z.lt Z.add]; clear; lia
    | cbv -[Z.le Z.lt Z.add]; clear; lia| exact P| exact Hs| apply fp_callsx_nog; repeat constructor| vm_compute; reflexivity| vm_compute; reflexivity].
Qed.
Lemma zlength_O_C1 : zlength O_C1 = 33. Proof. reflexivity. Qed.
Lemma zlength_O_C2 : zlength O_C2 = 21. Proof. reflexivity. Qed.
Lemma zlength_O_C3 : zlength O_C3 = 28. Proof. reflexivity. Qed.
Lemma zlength_O_C4 : zlength O_C4 = 8. Proof. reflexivity. Qed.
Lemma zlength_O_C5 : zlength O_C5 = 21. Proof. reflexivity. Qed.
Lemma zlength_O_C6 : zlength O_C6 = 21. Proof. reflexivity. Qed.
Lemma zlength_O_C7 : zlength O_C7 = 21. Proof. reflexivity. Qed.
Lemma zlength_O_C8 : zlength O_C8 = 4. Proof. reflexivity. Qed.
Lemma zlength_O_C9 : zlength O_C9 = 21. Proof. reflexivity. Qed.
Lemma zlength_O_C11 : zlength O_C11 = 21. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma emptyA_vargA : forall OW LB m, vargA_ok OW LB m (Z_to_bv 64 A_EMPTY_A) (PA_s []).
Proof.
  intros OW LB m. unfold vargA_ok, A_EMPTY_A. rewrite (unsigned_lit 686848) by (clear; lia).
  exists (zb [0; 0; 0; 0; 0; 0; 0]). change (zlength (@nil Z)) with 0. change (zlength (zb [0; 0; 0; 0; 0; 0; 0])) with 7.
  split; [constructor|]. split; [clear; lia|]. split; [clear; cbn; lia|].
  right. split; [clear; lia|]. split; [cbv; discriminate|]. split; [exact empty_lit_roA|].
  intros AR' Σ' m' H'. eapply (af_lib_acc_lit _ (@ar_AF AR') Σ' m' (0xa7b00, 1, 32)); [exact (@AH_art AR' _ _ _ _ H')| vm_compute; reflexivity| cbn; clear; lia| cbn; clear; lia].
Qed.
