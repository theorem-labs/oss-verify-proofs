(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from A/AE3h.v (vf_entry, the frame lemmas built on vf_file /
   vf_windows_ok): vf_file is musl vsnprintf's stack FILE at sp0 + 0x30 (write = sn_write) instead of the stderr FILE,
   the addresses are fm.asan's, the inline printf_core runs are calls of the printf_core contracts and the flush is a
   call of the sn_write contract (FMsnprintfI.v). *)
(* musl vfprintf 0x8ede0 on musl vsnprintf's FILE: the walk of fm's snprintf chain at the level of vfprintf, proved
   from the contracts of printf_core (both passes) and of the flush sn_write (f, 0, 0). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AE34 AF0l AE3e AE3f AE3g AE6g AE39 AE2p AE3i AE3h AF0m AE22 AF0x AE20 AE2y AE7f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMsnprintfI FMsnprintfK.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMsnprintfGI FMsnprintfGk FMsnprintfGt.
Import ListNotations.
Open Scope Z_scope.

(* ---- the walk's symbolic states: entry (cf. AE3h.v ss_vf), the runs between the calls ---- *)
Section r. Context {fx : YK11.FPState}.
Definition vfz (o : Z) : YP09.chunk := YP09.mkChunk (FO + o) (CVal 8 (SLit 0)).
(* the FILE and the cookie behind it as vsnprintf leaves them (vsn_fields), atom 33 = D, atom 34 = N - 1 *)
Definition vf_file_chunks : list YP09.chunk :=
 [ vfz 0; vfz 8; vfz 16; vfz 24; vfz 32; vfz 40; vfz 48; vfz 56; vfz 64;
   YP09.mkChunk (FO + 72) (CVal 8 (SLit A_SNW)); vfz 80;
   YP09.mkChunk (FO + 88) (CVal 8 (SOff 2 (FO + 0xff)));
   vfz 96; vfz 104; vfz 112; vfz 120; vfz 128;
   YP09.mkChunk (FO + 136) (CVal 4 (SLit 0)); YP09.mkChunk (FO + 140) (CVal 4 (SLit 0xffffffff));
   YP09.mkChunk (FO + 144) (CVal 4 (SLit 0xffffffff)); YP09.mkChunk (FO + 148) (CVal 4 (SLit 0));
   YP09.mkChunk (FO + 152) (CVal 8 (SOff 2 CKO));
   vfz 160; vfz 168; vfz 176; vfz 184; vfz 192; vfz 200; vfz 208; vfz 216; vfz 224;
   YP09.mkChunk (FO + 232) (CVal 8 (SOff 33 0)); YP09.mkChunk (FO + 240) (CVal 8 (SOff 34 0)) ].
Definition vf_stk0 : YP09.region := YP09.mkRegion (Some 2%nat) (- SNK_STK) 0 (-368) 0 [].
Definition vf_fil0 : YP09.region := YP09.mkRegion (Some 2%nat) FO (CKO + 16) FO (FO + 0xe8) vf_file_chunks.
Definition vf_got : YP09.region :=
  YP09.mkRegion None FM_GOT_canary (FM_GOT_canary + 8) 0 0 [YP09.mkChunk FM_GOT_canary (CVal 8 (SLit FM_canary))].
Definition vf_can : YP09.region :=
  YP09.mkRegion None FM_canary (FM_canary + 8) 0 0 [YP09.mkChunk FM_canary (CVal 8 (SOff 32 0))].
Definition vf_sr0 : list sv := sr_set sr_atoms (10%bv : bv 5) (SOff 2 FO).
Definition vf_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4) ] [] [].
Definition vs0 : sstate := mkSS A_VFP vf_sr0 [vf_stk0; vf_fil0; vf_got; vf_can] None vf_facts0.
Definition vRUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_g FUEL stop s.
Definition vRUN (s : sstate) := sym_runN tfibsegs tbl_g FUEL s.
(* the stack region without its writable window (the runs after the second printf_core pass store nothing there) *)
Definition win0 (r : YP09.region) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r).
(* f->write, read before the flush *)
Definition vwr : YP09.region :=
  YP09.mkRegion (Some 2%nat) (FO + 72) (FO + 80) 0 0 [YP09.mkChunk (FO + 72) (CVal 8 (SLit A_SNW))].
(* the FILE after the flush: flags and wpos as SNK out 0 has them *)
Definition vfl2 : YP09.region := YP09.mkRegion (Some 2%nat) FO (FO + 0xe8) FO (FO + 0xe8)
  [YP09.mkChunk FO (CVal 4 (SLit 0)); YP09.mkChunk (FO + 40) (CVal 8 (SOff 2 IBO))].
(* the boolean checks the proof reads off the computed states *)
(* every writable window lies in the stack below sp0 or in the FILE (AE3h.v band_winb / vf_windows_ok) *)
Definition vf_winb (t : option nat * Z * Z) : bool :=
  match t with
  | (Some 2%nat, lo, hi) => ((- SNK_STK <=? lo) && (hi <=? 0)) || ((FO <=? lo) && (hi <=? FO + 0xe8))
  | _ => false
  end || (snd t <=? snd (fst t)).
Definition vf_windows_ok (ss : sstate) : bool := forallb vf_winb (windows (ss_mem ss)).
Definition nowinb (ss : sstate) : bool := forallb (fun t => snd t <=? snd (fst t)) (windows (ss_mem ss)).
(* what kcall needs of the state at a call *)
Definition kcall_okb (ss : sstate) (r0 : YP09.region) (k : nat) (ra xlo xhi : Z) : bool :=
  match YP09.r_base r0 with Some 2%nat => true | _ => false end && (YP09.r_lo r0 =? - SNK_STK) &&
  (YP09.r_hi r0 =? 0) && (- SNK_STK <=? YP09.r_wlo r0) && (YP09.r_whi r0 <=? 0) &&
  forallb (chunk_inside r0) (YP09.r_chunks r0) &&
  sv_eqb (sr_get (ss_regs ss) 1) (SLit ra) && sv_eqb (sr_get (ss_regs ss) 2) (SOff 2 (-368)) &&
  ss_atoms_lt k ss && regions_wf (ss_mem (kafter k ss ra (-368) xlo xhi)) &&
  no_cdata (ss_mem (kafter k ss ra (-368) xlo xhi)) && mem_atoms_lt k (ss_mem (kafter k ss ra (-368) xlo xhi)) &&
  match ss_resv ss with None => true | Some _ => false end.
Definition chunk_isn (off : Z) (n : N) (v : sv) (c : YP09.chunk) : bool :=
  (YP09.c_off c =? off) && match YP09.c_val c with CVal m e => N.eqb m n && sv_eqb e v | _ => false end.
Definition kept_regs : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition kept_ok (ss : sstate) : bool :=
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) kept_regs.
(* two regions apart: both on the frame base and apart, or one on it and one low *)
Definition rdisjb (r1 r2 : YP09.region) : bool :=
  match YP09.r_base r1, YP09.r_base r2 with
  | Some 2%nat, Some 2%nat => (YP09.r_hi r1 <=? YP09.r_lo r2) || (YP09.r_hi r2 <=? YP09.r_lo r1)
  | Some 2%nat, None => (- SNK_STK <=? YP09.r_lo r1) && (0 <=? YP09.r_lo r2) && (YP09.r_hi r2 <=? 2 ^ 43)
  | None, Some 2%nat => (- SNK_STK <=? YP09.r_lo r2) && (0 <=? YP09.r_lo r1) && (YP09.r_hi r1 <=? 2 ^ 43)
  | None, None => (YP09.r_hi r1 <=? YP09.r_lo r2) || (YP09.r_hi r2 <=? YP09.r_lo r1)
  | _, _ => false
  end.

(* prologue, printf_core (0, ..) *)
Definition ve1 : sstate := Eval vm_compute in fst (vRUNTO A_PCORE vs0).
Lemma r_v1 : vRUNTO A_PCORE vs0 = (ve1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition ve1_st : YP09.region := Eval vm_compute in nth 0 (ss_mem ve1) vf_can.
Lemma ve1_mem : ss_mem ve1 = ve1_st :: [vf_fil0; vf_got; vf_can]. Proof. vm_compute. reflexivity. Qed.
Lemma vs0_win : vf_windows_ok vs0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ve1_weq : windows (ss_mem ve1) = windows (ss_mem vs0). Proof. vm_compute. reflexivity. Qed.
Lemma ve1_kok : kcall_okb ve1 ve1_st 35 RA_PCORE0 0 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ve1_regs : sr_get (ss_regs ve1) 3 = SOff 3 0 /\ sr_get (ss_regs ve1) 4 = SOff 4 0 /\
  sr_get (ss_regs ve1) 10 = SLit 0 /\ sr_get (ss_regs ve1) 11 = SOff 11 0 /\ sr_get (ss_regs ve1) 12 = SOff 2 (-368) /\
  sr_get (ss_regs ve1) 13 = SOff 2 (-272) /\ sr_get (ss_regs ve1) 14 = SOff 2 (-104).
Proof. vm_compute. repeat split. Qed.
Definition va1 : sstate := Eval vm_compute in kafter 35 ve1 RA_PCORE0 (-368) 0 0.
Lemma va1_eq : va1 = kafter 35 ve1 RA_PCORE0 (-368) 0 0. Proof. vm_compute. reflexivity. Qed.
Lemma ve1_r12 : sr_get (ss_regs ve1) 1 = SLit RA_PCORE0 /\ sr_get (ss_regs ve1) 2 = SOff 2 (-368).
Proof. vm_compute. split; reflexivity. Qed.
Definition ve2 : sstate := Eval vm_compute in fst (vRUNTO A_PCORE va1).
Lemma r_v2 : vRUNTO A_PCORE va1 = (ve2, RS_stopped (SR_branch BC_LT (SOff 39 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma va1_win : vf_windows_ok va1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ve2_weq : windows (ss_mem ve2) = windows (ss_mem va1). Proof. vm_compute. reflexivity. Qed.
(* printf_core (0, ..) returned 0: no __lockfile (lock = -1), the internal buffer (buf_size = 0), __towrite,
   printf_core (f, ..) *)
Definition vc2 : sstate := Eval vm_compute in add_cond ve2 (mkAC (neg_bc BC_LT) (SOff 39 0) (SLit 0)).
Lemma vc2_eq : vc2 = add_cond ve2 (mkAC (neg_bc BC_LT) (SOff 39 0) (SLit 0)). Proof. vm_compute. reflexivity. Qed.
Definition ve3 : sstate := Eval vm_compute in fst (vRUNTO A_PCORE vc2).
Lemma r_v3 : vRUNTO A_PCORE vc2 = (ve3, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma vc2_win : vf_windows_ok vc2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ve3_weq : windows (ss_mem ve3) = windows (ss_mem vc2). Proof. vm_compute. reflexivity. Qed.
Definition ve3_st : YP09.region := Eval vm_compute in nth 0 (ss_mem ve3) vf_can.
Definition ve3_fl : YP09.region := Eval vm_compute in nth 1 (ss_mem ve3) vf_can.
Lemma ve3_mem : ss_mem ve3 = [ve3_st] ++ ve3_fl :: [vf_got; vf_can]. Proof. vm_compute. reflexivity. Qed.
Lemma ve3_kok : kcall_okb (set_mem ve3 [ve3_st; vf_can]) ve3_st 51 RA_PCORE (-368) (-272) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ve3_regs : sr_get (ss_regs ve3) 1 = SLit RA_PCORE /\ sr_get (ss_regs ve3) 2 = SOff 2 (-368) /\
  sr_get (ss_regs ve3) 3 = SOff 3 0 /\ sr_get (ss_regs ve3) 4 = SOff 4 0 /\
  sr_get (ss_regs ve3) 10 = SOff 2 48 /\ sr_get (ss_regs ve3) 11 = SOff 11 0 /\ sr_get (ss_regs ve3) 12 = SOff 2 (-368) /\
  sr_get (ss_regs ve3) 13 = SOff 2 (-272) /\ sr_get (ss_regs ve3) 14 = SOff 2 (-104).
Proof. vm_compute. repeat split. Qed.
Lemma ve3_bases : YP09.r_base ve3_fl = Some 2%nat /\ YP09.r_base ve3_st = Some 2%nat.
Proof. vm_compute. split; reflexivity. Qed.
Definition va3 : sstate := Eval vm_compute in kafter 51 (set_mem ve3 [ve3_st; vf_can]) RA_PCORE (-368) (-368) (-272).
Lemma va3_eq : va3 = kafter 51 (set_mem ve3 [ve3_st; vf_can]) RA_PCORE (-368) (-368) (-272).
Proof. vm_compute. reflexivity. Qed.
Definition va3_st : YP09.region := Eval vm_compute in nth 0 (ss_mem va3) vf_can.
Lemma va3_mem : ss_mem va3 = va3_st :: [vf_can]. Proof. vm_compute. reflexivity. Qed.
(* to f->write = sn_write *)
Definition vi3 : sstate := set_mem va3 [win0 va3_st; vwr; vf_can].
Definition ve4 : sstate := Eval vm_compute in fst (vRUNTO A_SNW vi3).
Lemma r_v4 : vRUNTO A_SNW vi3 = (ve4, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma vi3_win : vf_windows_ok vi3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vi3_nowin : nowinb vi3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ve4_weq : windows (ss_mem ve4) = windows (ss_mem vi3). Proof. vm_compute. reflexivity. Qed.
Definition ve4_st : YP09.region := Eval vm_compute in nth 0 (ss_mem ve4) vf_can.
Lemma ve4_mem : ss_mem ve4 = ve4_st :: [vwr; vf_can]. Proof. vm_compute. reflexivity. Qed.
Lemma ve4_kok : kcall_okb ve4 ve4_st 67 RA_FLUSH (-352) (-272) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ve4_regs : sr_get (ss_regs ve4) 1 = SLit RA_FLUSH /\ sr_get (ss_regs ve4) 2 = SOff 2 (-368) /\
  sr_get (ss_regs ve4) 3 = SOff 3 0 /\ sr_get (ss_regs ve4) 4 = SOff 4 0 /\
  sr_get (ss_regs ve4) 10 = SOff 2 48 /\ sr_get (ss_regs ve4) 11 = SLit 0 /\ sr_get (ss_regs ve4) 12 = SLit 0.
Proof. vm_compute. repeat split. Qed.
Definition va4 : sstate := Eval vm_compute in kafter 67 ve4 RA_FLUSH (-368) (-352) (-272).
Lemma va4_eq : va4 = kafter 67 ve4 RA_FLUSH (-368) (-352) (-272). Proof. vm_compute. reflexivity. Qed.
Definition va4_st : YP09.region := Eval vm_compute in nth 0 (ss_mem va4) vf_can.
Lemma va4_mem : ss_mem va4 = [va4_st] ++ vwr :: [vf_can]. Proof. vm_compute. reflexivity. Qed.
(* the FILE reset, the result, the canary check, the epilogue *)
Definition vi4 : sstate := set_mem va4 [va4_st; vfl2; vf_can].
Definition ve5 : sstate := Eval vm_compute in fst (vRUN vi4).
Lemma r_v5 : vRUN vi4 = (ve5, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Lemma vi4_win : vf_windows_ok vi4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ve5_weq : windows (ss_mem ve5) = windows (ss_mem vi4). Proof. vm_compute. reflexivity. Qed.
Lemma ve5_ret : ss_resv ve5 = None /\ clookup tbl_g (ss_pc ve5) = Some RET_WORD_r.
Proof. vm_compute. split; reflexivity. Qed.
Lemma ve5_kept : kept_ok ve5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ve5_regs : sr_get (ss_regs ve5) 1 = SOff 1 0 /\
  sr_get (ss_regs ve5) 10 = SAlu ALU_OR (SLit 0) (SAlu ALU_OR (SLit 0) (SOff 55 0)).
Proof. vm_compute. split; reflexivity. Qed.
Lemma regions_r : forallb (rdisjb vwr) [win0 va3_st; vf_can] = true /\ forallb (rdisjb vfl2) [va4_st; vf_can] = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma regions_wf_r : region_wf vwr = true /\ region_wf vfl2 = true. Proof. vm_compute. split; reflexivity. Qed.
End r.

(* ---- the frame and region lemmas of the walk (AE3h.v VI_run / vf_windows_sound / vf_band_present on vsnprintf's
   FILE), the call step over a sink contract, the transport of the destination facts ---- *)
Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis APCORE0 : apcore0_realizesU B A_PCORE.
Hypothesis APCORE : apcore_realizesU B A_PCORE.
Hypothesis AFLUSH : asnflush_realizesU B A_SNW.

Lemma snk_frame_weak : forall ly S U W mem0 md0 sp0 top (X1 X2 : Z -> Prop) mem md,
  snk_frame B ly S U W mem0 md0 sp0 top X1 mem md -> (forall a, X1 a -> X2 a) ->
  snk_frame B ly S U W mem0 md0 sp0 top X2 mem md.
Proof.
intros ly S U W mem0 md0 sp0 top X1 X2 mem md (HA & Hsb & Hp & Hfr & Hpm) HX.
split; [exact HA|]. split; [exact Hsb|]. split; [exact Hp|]. split; [|exact Hpm].
intros a Hr H1 H2. apply Hfr; [exact Hr | exact H1 | intros Hx; exact (H2 (HX a Hx))].
Qed.
Lemma vf_windows_sound : forall E ss sp0 a, vf_windows_ok ss = true -> bv_unsigned (ew E 2) = sp0 ->
  in_wrange E (ss_mem ss) a -> (sp0 - SNK_STK <= a < sp0) \/ (sp0 + FO <= a < sp0 + FO + 0xe8).
Proof.
intros E ss sp0 a Hb Hsp Hin.
destruct (in_wrange_windows E _ a Hin) as (bb & lo & hi & Ht & Hr).
unfold vf_windows_ok in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht). unfold vf_winb in Hb.
apply orb_prop in Hb as [Hb|Hb].
- destruct bb as [[|[|[|nn]]]|]; try discriminate Hb. cbn [base_val] in Hr. rewrite Hsp in Hr.
  apply orb_prop in Hb as [Hb|Hb]; apply andb_prop in Hb as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2;
  [left | right]; lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
Lemma nowin : forall E ss a, nowinb ss = true -> ~ in_wrange E (ss_mem ss) a.
Proof.
intros E ss a Hb Hin. destruct (in_wrange_windows E _ a Hin) as (bb & lo & hi & Ht & Hr).
unfold nowinb in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht). cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
(* a Theorem Labs lane's FMsnprintfFw.v win_writable / in_wrange_windows_eq *)
Lemma vwin_writable : forall E ss ms a, st_ok tfibsegs E ss ms -> in_wrange E (ss_mem ss) a ->
  writable_at tfibsegs (ms_mem ms) a.
Proof.
intros E ss ms a HS (r & Hin & Ha).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _).
pose proof (proj1 (Forall_forall _ _) Hok r Hin) as (_ & _ & Hw & _).
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.
Lemma vwin_eq : forall E rs rs' a, windows rs' = windows rs -> in_wrange E rs a -> in_wrange E rs' a.
Proof.
intros E rs rs' a Hw Hin. destruct (in_wrange_windows E rs a Hin) as (bb & lo & hi & Ht & Hr).
rewrite <- Hw in Ht. unfold windows in Ht. apply in_map_iff in Ht as (r & Er & Hr').
injection Er as E1 E2 E3. exists r. split; [exact Hr'|]. rewrite E1, E2, E3. exact Hr.
Qed.
(* the frame after a run of vfprintf's own code (AE3h.v VI_run, with g_frame_run) *)
Lemma vf_after_run : forall ly S U W mem0 md0 sp0 (XW : Z -> Prop) E ss ss' ms ms1 md mat1,
  snk_base B ly S U W mem0 md0 sp0 ->
  (forall a, sp0 + FO <= a < sp0 + FO + 0xe8 -> XW a) ->
  bv_unsigned (ew E 2) = sp0 ->
  vf_windows_ok ss = true -> windows (ss_mem ss') = windows (ss_mem ss) ->
  st_ok tfibsegs E ss' (restrict (w_H W) ms1) ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) ->
  snk_frame B ly S U W mem0 md0 sp0 sp0 XW (ms_mem ms) md ->
  snk_frame B ly S U W mem0 md0 sp0 sp0 XW (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md).
Proof.
intros ly S U W mem0 md0 sp0 XW E ss ss' ms ms1 md mat1 Hb HX Hsp Hwok Hweq HS1 HF FI.
pose proof Hb as (_ & _ & H44 & _ & _ & _ & H47 & Hkh & _ & _).
assert (HSS : SNK_STK = 9104) by reflexivity.
apply (g_frame_run B LAWS ly S U W mem0 md0 sp0 sp0 XW Hb (ms_mem ms) md (ms_mem ms1) mat1 E (ss_mem ss) FI).
- intros a Hin. unfold snk_band. destruct (vf_windows_sound E ss sp0 a Hwok Hsp Hin) as [Hw|Hw].
  + split; [lia | left; lia].
  + split; [unfold FO in *; lia | right; apply HX; exact Hw].
- exact HF.
- intros a Ha. unfold snk_band in Ha. destruct (in_wrangeb_dec E (ss_mem ss) a) as [Hin|Hin].
  + apply (vwin_eq E _ (ss_mem ss') a Hweq) in Hin.
    pose proof (vwin_writable E ss' (restrict (w_H W) ms1) a HS1 Hin) as Hwr. cbn [restrict ms_mem] in Hwr.
    apply (apresent_of_writable (w_H W) (ms_mem ms1) a);
      [unfold kHighMemBeg in *; lia | apply high_not_img; unfold kLowMemEnd, kHighMemBeg in *; lia | exact Hwr].
  + destruct FI as (_ & _ & Hp & _). pose proof (Hp a ltac:(unfold snk_band; lia)) as [Hh [bb Hbb]].
    split; [exact Hh|]. exists bb.
    rewrite (HF (Z_to_bv 64 a)); [exact Hbb|]. rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia). exact Hin.
Qed.
(* the stack region with its writable window dropped *)
Lemma st_ok_win0 : forall E ss ms r0 rest, st_ok tfibsegs E ss ms -> ss_mem ss = r0 :: rest ->
  st_ok tfibsegs E (set_mem ss (win0 r0 :: rest)) ms.
Proof.
intros E ss ms r0 rest (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- cbn [regions_wf] in *. apply andb_prop in Hwf as [Ha Hb]. rewrite Hb, andb_true_r.
  unfold region_wf in *. unfold win0. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  apply andb_prop in Ha as [Ha Hc]. apply andb_prop in Ha as [Ha _]. rewrite Ha. cbn [orb andb].
  unfold chunk_inside in *. cbn [YP09.r_lo YP09.r_hi]. exact Hc.
- inversion Hok as [|x l Hr Hl]; subst. constructor; [|exact Hl].
  destruct Hr as (Hlo & Hhi & _ & Hcs). unfold region_ok, win0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [exact Hlo|]. split; [exact Hhi|]. split; [intros o Ho; lia | exact Hcs].
- cbn [pairwise_disjoint] in Hpd |- *. destruct Hpd as [Hd Hp]. split; [|exact Hp].
  apply all_disjoint_forall. apply all_disjoint_forall in Hd. eapply Forall_impl; [|exact Hd]. intros r' Hr'. exact Hr'.
Qed.
Lemma rdisjb_ok : forall E sp0 r1 r2, bv_unsigned (ew E 2) = sp0 -> 2 ^ 44 <= sp0 -> rdisjb r1 r2 = true ->
  extent_disjoint E r1 r2.
Proof.
intros E sp0 [b1 lo1 hi1 wl1 wh1 c1] [b2 lo2 hi2 wl2 wh2 c2] Hsp H44 Hb. unfold rdisjb in Hb. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi] in *. assert (HSS : SNK_STK = 9104) by reflexivity.
destruct b1 as [[|[|[|n1]]]|]; destruct b2 as [[|[|[|n2]]]|]; try discriminate Hb; cbn [base_val] in *; rewrite ?Hsp;
repeat match goal with H : (_ || _)%bool = true |- _ => apply orb_prop in H | H : (_ && _)%bool = true |- _ => apply andb_prop in H end;
repeat match goal with H : _ \/ _ |- _ => destruct H | H : _ /\ _ |- _ => destruct H end;
repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end; lia.
Qed.
Lemma rdisj_all : forall E sp0 r rs, bv_unsigned (ew E 2) = sp0 -> 2 ^ 44 <= sp0 -> forallb (rdisjb r) rs = true ->
  Forall (extent_disjoint E r) rs.
Proof.
intros E sp0 r rs Hsp H44 Hb. apply Forall_forall. intros x Hx. rewrite forallb_forall in Hb.
exact (rdisjb_ok E sp0 r x Hsp H44 (Hb x Hx)).
Qed.
Lemma chunk_isn_in : forall off n v cs, existsb (chunk_isn off n v) cs = true -> In (YP09.mkChunk off (CVal n v)) cs.
Proof.
intros off n v cs H. apply existsb_exists in H as ([o cv] & Hc & Hb). unfold chunk_isn in Hb.
cbn [YP09.c_off YP09.c_val] in Hb. apply andb_prop in Hb as [Ho Hv]. apply Z.eqb_eq in Ho.
destruct cv as [m e| | |]; try discriminate. apply andb_prop in Hv as [Hm He].
apply N.eqb_eq in Hm. apply sv_eqb_eq in He. subst. exact Hc.
Qed.
Lemma havoc_lt : forall E k ws i, (i < k)%nat -> ew (havoc E k ws) i = ew E i.
Proof. intros E k ws i Hi. unfold havoc. cbn [ew]. apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity. Qed.
Lemma slot_of : forall (W : world tfibsegs) E ss ms i r sp0 off (n : N) e v,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> bv_unsigned (ew E 2) = sp0 ->
  nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some 2%nat ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 + off) (N.to_nat n) v.
Proof.
intros W E ss ms i r sp0 off n e v HS Hsp Hi Hb Hc He Hv Hn.
pose proof (g_slot W E ss ms i r off n e v HS Hi Hc He Hv Hn) as X. rewrite Hb in X. cbn [base_val] in X.
rewrite Hsp in X. exact X.
Qed.
Lemma or0_denot : forall E (e : sv) z, sv_denot E e = w64 z -> 0 <= z < 2 ^ 64 ->
  sv_denot E (SAlu ALU_OR (SLit 0) (SAlu ALU_OR (SLit 0) e)) = w64 z.
Proof.
intros E e z He Hz. rewrite denot_lit_U, !U_SAlu, !U_SLit.
assert (Ue : U E e = z) by (unfold U; rewrite He; apply unsigned_lit_small; exact Hz).
rewrite Ue. cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_0_l by lia. rewrite !Z.lor_0_l.
rewrite !Z.mod_small by lia. reflexivity.
Qed.
(* SNK reads the memory pointwise *)
Lemma SNK_same : forall (W : world tfibsegs) (m m' : word -> option byte) sp0 D N out b,
  (forall x, m' x = m x) -> SNK W m sp0 D N out b -> SNK W m' sp0 D N out b.
Proof.
intros W m m' sp0 D N out b Hm Hs.
assert (AV : forall a, aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) by (intros a; apply aview_same; apply Hm).
assert (VM : forall a n v, val_mem tfibsegs (mrestrict (w_H W) m) a n v -> val_mem tfibsegs (mrestrict (w_H W) m') a n v)
  by (intros a n v Hv; apply (val_mem_kept (w_H W) (w_H W) m m'); [intros k _; apply AV | exact Hv]).
destruct Hs as (S0 & S32 & S40 & S56 & S72 & S88 & S144 & S152 & SC0 & SC8 & SIB & SD & SDn & Hrest).
unfold SNK. cbv zeta.
split; [apply VM; exact S0|]. split; [apply VM; exact S32|]. split; [apply VM; exact S40|].
split; [apply VM; exact S56|]. split; [apply VM; exact S72|]. split; [apply VM; exact S88|].
split; [apply VM; exact S144|]. split; [apply VM; exact S152|]. split; [apply VM; exact SC0|].
split; [apply VM; exact SC8|].
split; [intros i Hi; rewrite AV; exact (SIB i Hi)|]. split; [intros i Hi; rewrite AV; exact (SD i Hi)|].
split; [rewrite AV; exact SDn | exact Hrest].
Qed.
(* the destination's facts at a memory reached under vfprintf's frame *)
Lemma snk_dest_xfer : forall ly S U W mem md mem' md' sp0 D M,
  snk_base B ly S U W mem md sp0 -> snk_dest B ly S W mem D M ->
  snk_frame B ly S U W mem md sp0 sp0 (vf_xw sp0 D M) mem' md' -> snk_dest B ly S W mem' D M.
Proof.
intros ly S U W mem md mem' md' sp0 D M Hb Hdst (_ & _ & _ & Hfr & Hpm).
pose proof Hb as (HA & Hac & H44 & H16 & Hlo & Hhi & H47 & Hkh & _ & _).
pose proof Hdst as (HD0 & HDhi & HM30 & HDcan & HDw & HDam & HDra & HDhull).
pose proof ac_bounds as ACB.
assert (HSS : SNK_STK = 9104) by reflexivity.
assert (KS : forall s, SHADOW_OFF <= s < kHighMemBeg -> aview tfibsegs (w_H W) mem' s = aview tfibsegs (w_H W) mem s).
{ intros s Hs. apply Hfr; [unfold SHADOW_OFF, kHighMemBeg in *; lia | unfold kHighMemBeg in *; lia |].
  unfold vf_xw, dst_xw. intros [X|X]; [unfold CKO, FO in X; unfold kHighMemBeg in *; lia|].
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. }
split; [exact HD0|]. split; [exact HDhi|]. split; [exact HM30|]. split; [exact HDcan|].
split; [|split; [exact HDam|split]].
- intros a Ha. destruct (HDw a Ha) as (Hw & Ho & Hr). split; [|split; [exact Ho | exact Hr]].
  exact (writable_xfer (w_H W) mem mem' a Hw (Hpm a)).
- intros x Hx. destruct (HDra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite KS; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg, amem_range, kLowMemEnd, kHighMemEnd in *.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)). lia.
- intros s Hs. rewrite KS; [exact (HDhull s Hs)|].
  unfold shadow_addr, SHADOW_OFF, kHighMemBeg, amem_range, kLowMemEnd, kHighMemEnd in *.
  pose proof (Z.div_pos D 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (D + M - 1) (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + D / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + D / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + (D + M - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + (D + M - 1) / 8) 8 ltac:(lia)).
  lia.
Qed.
(* a call of a sink contract met by the walk at sp0 - 368 (kcall, with the callee's snk_post and FMsnprintfI's frame) *)
Lemma vf_kcall : forall ly S U W mem0 md0 sp0 (XWf : Z -> Prop) E ss ms md r0 rest k ra xlo xhi
    (XWk XWc : Z -> Prop) topc v (Q : (word -> option byte) -> Prop),
  snk_base B ly S U W mem0 md0 sp0 ->
  snk_frame B ly S U W mem0 md0 sp0 sp0 XWf (ms_mem ms) md ->
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> bv_unsigned (ew E 2) = sp0 ->
  ss_mem ss = r0 :: rest -> kcall_okb ss r0 k ra xlo xhi = true -> 0 <= ra < 2 ^ 64 ->
  (forall a, XWk a -> sp0 - SNK_STK <= a < sp0 -> sp0 + xlo <= a < sp0 + xhi) ->
  (forall a, (sp0 - SNK_STK <= a < topc) \/ XWc a -> (sp0 - SNK_STK <= a < sp0 - 368) \/ XWk a) ->
  (forall a, XWk a -> (sp0 - SNK_STK <= a < sp0) \/ XWf a) ->
  (forall r a, In r rest -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     0 <= a < 2 ^ 64 /\ ~ (sp0 - SNK_STK <= a < sp0 - 368) /\ ~ XWk a) ->
  (forall r a, In r rest ->
     base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
     apresent (w_H W) (ms_mem ms) a) ->
  SRr tfibsegs W (cfg_at tfibsegs (ss_pc ss) (ms_regs ms) (ms_mem ms) md)
    (snk_post B ly S U W (ms_regs ms) (ms_mem ms) md sp0 topc XWc v Q) ->
  SRr tfibsegs W (mkCfg ms md) (fun W' c' => W' = W /\ exists ms2 mat2,
    c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
    st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (kafter k ss ra (-368) xlo xhi) (restrict (w_H W) ms2) /\
    snk_frame B ly S U W mem0 md0 sp0 sp0 XWf (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
    getr (ms_regs ms2) 10 = w64 v /\ Q (ms_mem ms2)).
Proof.
intros ly S U W mem0 md0 sp0 XWf E ss ms md r0 rest k ra xlo xhi XWk XWc topc v Q Hb FI HS Usp Hmem0 Hok Hra
  HXs CIN XIN Hrest HrestW HC.
unfold kcall_okb in Hok.
apply andb_prop in Hok as [Hok Hrv']. apply andb_prop in Hok as [Hok Hma2]. apply andb_prop in Hok as [Hok Hnc2].
apply andb_prop in Hok as [Hok Hwf2]. apply andb_prop in Hok as [Hok Hat]. apply andb_prop in Hok as [Hok S2].
apply andb_prop in Hok as [Hok S1]. apply andb_prop in Hok as [Hok Hci0]. apply andb_prop in Hok as [Hok Hwhi0].
apply andb_prop in Hok as [Hok Hwlo0]. apply andb_prop in Hok as [Hok Hhi0]. apply andb_prop in Hok as [Hb0 Hlo0].
apply sv_eqb_eq in S1. apply sv_eqb_eq in S2. apply Z.eqb_eq in Hlo0. apply Z.eqb_eq in Hhi0.
apply Z.leb_le in Hwlo0. apply Z.leb_le in Hwhi0.
assert (Hrv : ss_resv ss = None) by (destruct (ss_resv ss); [discriminate | reflexivity]).
assert (Hb0' : YP09.r_base r0 = Some 2%nat) by (destruct (YP09.r_base r0) as [[|[|[|n]]]|]; try discriminate; reflexivity).
pose proof Hb as (_ & _ & H44 & _ & _ & _ & H47 & _ & _ & _).
assert (HSS : SNK_STK = 9104) by reflexivity.
pose proof FI as (_ & _ & Hps & _ & _).
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
eapply SRr_mono.
{ refine (kcall W E ss ms md sp0 SNK_STK r0 rest k ra (-368) xlo xhi (SNK_STK - 368) XWk
    (fun regs2 mem2 md2 => snk_frame B ly S U W (ms_mem ms) md sp0 topc XWc mem2 md2 /\ getr regs2 10 = w64 v /\ Q mem2)
    HS Hrv Usp Hmem0 Hb0' Hlo0 Hhi0 Hwlo0 Hwhi0 S1 S2 Hat Hwf2 Hnc2 Hma2 Hci0 _ _ _ _ _ _ _ _ _ _).
  - lia. - lia. - lia. - lia. - lia.
  - exact HXs.
  - intros r a Hr Ha. destruct (Hrest r a Hr Ha) as (H1 & H2 & H3). split; [exact H1|].
    split; [intros Hc; apply H2; lia | exact H3].
  - exact HrestW.
  - intros a Ha. apply Hps. unfold snk_band. lia.
  - eapply SRr_mono; [exact HC|].
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HF2 & HP & H10 & HQ).
    pose proof HF2 as (_ & Hsb2 & _ & Hfr2 & Hpm2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [unfold raZ; rewrite R1, unsigned_lit_small by lia; reflexivity|].
    split; [exact HP|]. split; [exact Hsb2|].
    split; [|split; [exact Hpm2 | split; [exact HF2 | split; [exact H10 | exact HQ]]]].
    intros a Hr H1 H2. apply Hfr2; [exact Hr | |].
    + intros Hc. destruct (CIN a (or_introl Hc)) as [Y|Y]; [apply H1; lia | exact (H2 Y)].
    + intros Hc. destruct (CIN a (or_intror Hc)) as [Y|Y]; [apply H1; lia | exact (H2 Y)]. }
cbv beta. intros W' c' _ (-> & ms2 & mat2 & -> & HS2 & HP2 & Hfr2 & Hpm2 & HF2 & H10 & HQ).
split; [reflexivity|]. exists ms2, mat2. split; [reflexivity|]. split; [exact HS2|].
split; [|split; [exact H10 | exact HQ]].
pose proof HF2 as (HA2 & Hsb2 & Hps2 & _ & _).
apply (g_frame_step B ly S U W mem0 md0 sp0 sp0 XWf (ms_mem ms) md _ _ FI HA2 Hsb2 Hps2).
- intros a Hr H1 H2. apply Hfr2; [exact Hr | intros Hc; apply H1; lia |].
  intros Hx. destruct (XIN a Hx) as [Y|Y]; [exact (H1 Y) | exact (H2 Y)].
- exact Hpm2.
Qed.

(* ---- the walk: the contract's premises as section hypotheses, one lemma per stretch, from the last to the first ---- *)
Section w.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (sp0 D N M f : Z) (ps : list fpiece) (P : Z) (args out : list Z) (cval : Z).
Hypothesis HPRE : gl_pre B ly S U W mem md sp0 D N M f ps P args out.
Hypothesis HREG : snk_regs B regs sp0.
Hypothesis G10 : getr regs 10 = w64 (sp0 + FO).
Hypothesis G11 : getr regs 11 = w64 f.
Hypothesis G12 : getr regs 12 = w64 P.
Hypothesis HVF : vsn_file W mem sp0 D N.
Hypothesis HCAN : val_mem tfibsegs (mrestrict (w_H W) mem) FM_canary 8 cval.
Hypothesis HCV : 0 <= cval < 2 ^ 64.
(* the entry environment: the registers, the canary value, the cookie {D, N - 1} *)
Definition vE0 : env := Ereg regs [Z_to_bv 64 cval; Z_to_bv 64 D; Z_to_bv 64 (N - 1)].
(* the cells vfprintf's own code writes above sp0: the FILE and the cookie *)
Definition fxw (a : Z) : Prop := sp0 + FO <= a < sp0 + CKO + 16.
(* an environment of the walk: the entry atoms kept *)
Definition vEK (E : env) : Prop := forall i, (i < 35)%nat -> ew E i = ew vE0 i.

Lemma w_base : snk_base B ly S U W mem md sp0.
Proof. exact (proj1 HPRE). Qed.
Lemma w_dest : snk_dest B ly S W mem D M.
Proof. destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X). exact X. Qed.
Lemma w_lay : 2 ^ 44 <= sp0 /\ sp0 mod 16 = 0 /\ sp0 + 0x200 <= 2 ^ 47 /\ kHighMemBeg <= sp0 - SNK_STK /\
  alloc_ceiling <= sp0 - SNK_STK /\ sp0 + 0x200 <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof.
pose proof w_base as (HA & Hac & H44 & H16 & Hlo & Hhi & H47 & Hkh & _).
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
assert (HSS : SNK_STK = 9104) by reflexivity.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.
Lemma w_nums : 0 < D /\ D + M <= alloc_ceiling /\ Z.of_nat (length out) + 1 <= M /\ M <= N /\ N <= 2 ^ 30 /\
  (D + M <= FM_canary \/ FM_canary + 8 <= D) /\ amem_range D M /\ sp0 + 0x200 <= P /\
  P + 8 * Z.of_nat (length args) <= ly_stk_hi ly /\ alloc_ceiling < 2 ^ 47.
Proof.
destruct HPRE as (_ & _ & _ & _ & _ & HP1 & HP2 & _ & _ & HM & HN & (HD0 & HDhi & _ & HDcan & _ & HDam & _)).
pose proof ac_bounds as ACB.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HDcan|].
split; [exact HDam|]. split; [lia|]. split; lia.
Qed.
Lemma E0_2 : bv_unsigned (ew vE0 2) = sp0.
Proof.
pose proof w_lay as (H44 & _ & H47 & _). destruct HREG as (_ & H2 & _).
unfold vE0. rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), H2. apply unsigned_lit_small. lia.
Qed.
Lemma EK_0 : vEK vE0. Proof. intros i _. reflexivity. Qed.
Lemma EK_2 : forall E, vEK E -> bv_unsigned (ew E 2) = sp0.
Proof. intros E HK. rewrite (HK 2%nat ltac:(lia)). exact E0_2. Qed.
Lemma EK_reg : forall E i (r : bv 5), vEK E -> (i < 32)%nat -> Z.of_nat i = bv_unsigned r ->
  sv_denot E (SOff i 0) = getr regs r.
Proof.
intros E i r HK Hi Hr. cbn [sv_denot]. rewrite (HK i ltac:(lia)), Z.add_0_r. unfold vE0.
rewrite (ew_Ereg_nat regs _ i r Hr). apply Z_to_bv_bv_unsigned.
Qed.
Lemma EK_x : forall E j, vEK E -> (j < 3)%nat ->
  ew E (32 + j) = nth j [Z_to_bv 64 cval; Z_to_bv 64 D; Z_to_bv 64 (N - 1)] (Z_to_bv 64 0).
Proof. intros E j HK Hj. rewrite (HK (32 + j)%nat ltac:(lia)). unfold vE0. apply ew_Ereg_extra. Qed.
Lemma EK_sp : forall E x, vEK E -> sv_denot E (SOff 2 x) = w64 (sp0 + x).
Proof. intros E x HK. cbn [sv_denot]. rewrite (EK_2 E HK). reflexivity. Qed.
Lemma EK_havoc : forall E k ws, vEK E -> (35 <= k)%nat -> vEK (havoc E k ws).
Proof. intros E k ws HK Hk i Hi. rewrite havoc_lt by lia. apply HK. exact Hi. Qed.
(* the registers every call below vfprintf starts with, at sp0 - 368 *)
Lemma w_regs : forall E ss ms ra, vEK E -> st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sr_get (ss_regs ss) 1 = SLit ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 -> sr_get (ss_regs ss) 2 = SOff 2 (-368) ->
  sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
  snk_regs B (ms_regs ms) (sp0 + OSP_PC).
Proof.
intros E ss ms ra HK HS S1 Hra Hra2 S2 S3 S4. destruct HREG as (_ & _ & H3 & H4).
split; [|split; [|split]].
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1. apply ret_ok_lit; assumption.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2, (EK_sp E (-368) HK). reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3, (EK_reg E 3 3%bv HK ltac:(lia) eq_refl). exact H3.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4, (EK_reg E 4 4%bv HK ltac:(lia) eq_refl). exact H4.
Qed.
(* gl_pre at a memory that differs from the entry one only in the stack below sp0 and in the FILE *)
Lemma w_pre : forall mem' md', snk_frame B ly S U W mem md sp0 sp0 fxw mem' md' ->
  gl_pre B ly S U W mem' md' sp0 D N M f ps P args out.
Proof.
intros mem' md' (HA & _ & Hps & Hfr & Hpm).
pose proof w_lay as (H44 & H16 & H47 & Hkh & Hac & Htop & Hhs).
pose proof w_nums as (HD0 & HDac & HM1 & HM2 & HN & HDcan & HDam & HP1 & HP2 & ACB).
assert (HSS : SNK_STK = 9104) by reflexivity.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < P) ->
  aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. apply Hfr; [exact Ha | lia | unfold fxw, CKO, FO; lia]. }
apply (gl_pre_xfer B LAWS TB ly S U W mem md mem' md' sp0 D N M f ps P args out HPRE HA Hps).
- intros a Ha Hn _. exact (KEEP a Ha Hn).
- left. apply KEEP; lia.
- exact Hpm.
Qed.
(* the FILE and the destination agree with the frame: XW of the whole walk *)
Lemma vf_xw_far : forall a, vf_xw sp0 D M a -> a < SHADOW_OFF \/ kHighMemBeg <= a.
Proof.
intros a Ha. pose proof w_lay as (H44 & H16 & H47 & Hkh & Hac & Htop & Hhs).
pose proof w_nums as (HD0 & HDac & HM1 & HM2 & HN & HDcan & HDam & HP1 & HP2 & ACB).
assert (HSS : SNK_STK = 9104) by reflexivity.
destruct Ha as [Ha|Ha]; [right; unfold FO in Ha; lia|]. unfold dst_xw in Ha.
unfold amem_range, kLowMemEnd, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

(* the flags, the result, the canary check, the epilogue, the return *)
Lemma w_s5 : forall ms md4 E, vEK E -> ew E 55 = w64 (Z.of_nat (length out)) ->
  st_ok tfibsegs E vi4 (restrict (w_H W) ms) ->
  snk_frame B ly S U W mem md sp0 sp0 (vf_xw sp0 D M) (ms_mem ms) md4 ->
  SNK W (ms_mem ms) sp0 D N out 0 ->
  SRr tfibsegs W (mkCfg ms md4) (gl_post B ly S U W regs mem md sp0 sp0 (vf_xw sp0 D M) D out).
Proof.
intros ms md4 E HK E55 HS FI HSNK.
pose proof w_lay as (H44 & H16 & H47 & Hkh & Hac & Htop & Hhs).
pose proof w_nums as (HD0 & HDac & HM1 & HM2 & HN & HDcan & HDam & HP1 & HP2 & ACB).
assert (HSS : SNK_STK = 9104) by reflexivity.
pose proof (EK_2 E HK) as E2.
assert (HX : forall a, sp0 + FO <= a < sp0 + FO + 0xe8 -> vf_xw sp0 D M a) by (intros a Ha; left; unfold CKO; lia).
eapply SRr_bind; [exact (g_phase W E vi4 ve5 _ ms md4 HS r_v5)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
change (st_ok tfibsegs E ve5 (restrict (w_H W) ms1)) in HS1.
pose proof (vf_after_run ly S U W mem md sp0 (vf_xw sp0 D M) E vi4 ve5 ms ms1 md4 mat1 w_base HX E2 vi4_win ve5_weq
  HS1 HF1 FI) as FI1.
set (md5 := with_vm_backing (m_vm_lazy md4) mat1 md4) in *.
apply (g_ret W E ve5 ms1 md5 _ HS1 (proj1 ve5_ret) (proj2 ve5_ret)).
intros mat'.
pose proof ve5_regs as (Q1 & Q10).
split; [reflexivity|].
exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md5) mat' md5).
assert (R1 : getr (ms_regs ms1) 1 = getr regs 1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS1), Q1. exact (EK_reg E 1 1%bv HK ltac:(lia) eq_refl). }
split.
{ unfold cfg_at. rewrite R1. destruct HREG as (Hra & _). unfold YK0s.ret_ok in Hra. rewrite Hra.
  unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ apply (g_frame_run B LAWS ly S U W mem md sp0 sp0 (vf_xw sp0 D M) w_base (ms_mem ms1) md5 (ms_mem ms1) mat' E [] FI1).
  - intros a (r & Hr & _). destruct Hr.
  - intros x _. reflexivity.
  - destruct FI1 as (_ & _ & Hp & _). exact Hp. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hin : In r kept_regs) by (unfold kept_regs; cbn [In]; lia).
  pose proof ve5_kept as K. unfold kept_ok in K. rewrite forallb_forall in K. specialize (K r Hin). apply sv_eqb_eq in K.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ (Z_to_bv 5 r) HS1), K.
  apply (EK_reg E); [exact HK | lia |].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
split.
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS1), Q10. apply or0_denot; [| lia].
  cbn [sv_denot]. rewrite E55, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
intros i Hi.
pose proof HSNK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SD & SDn & _).
assert (KD : forall a, D <= a < D + M -> aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) (ms_mem ms) a).
{ intros a Ha. apply aview_same. apply HF1. rewrite unsigned_lit_small by lia.
  intros Hin. destruct (vf_windows_sound E vi4 sp0 a vi4_win E2 Hin) as [X|X]; unfold FO in X; lia. }
rewrite KD by lia.
destruct (Z.eq_dec i (Z.of_nat (length out))) as [->|Hne].
- rewrite Nat2Z.id, app_nth2, Nat.sub_diag by lia. cbn [nth].
  replace (D + Z.of_nat (length out)) with (D + (Z.of_nat (length out) - 0)) by lia. exact SDn.
- rewrite app_nth1 by lia. apply SD. lia.
Qed.

(* f->write = sn_write (f, 0, 0), then the end *)
Lemma w_s4 : forall ms md3 E b, vEK E -> ew E 55 = w64 (Z.of_nat (length out)) ->
  st_ok tfibsegs E vi3 (restrict (w_H W) ms) ->
  snk_frame B ly S U W mem md sp0 sp0 (vf_xw sp0 D M) (ms_mem ms) md3 ->
  SNK W (ms_mem ms) sp0 D N out b ->
  SRr tfibsegs W (mkCfg ms md3) (gl_post B ly S U W regs mem md sp0 sp0 (vf_xw sp0 D M) D out).
Proof.
intros ms md3 E b HK E55 HS FI HSNK.
pose proof w_lay as (H44 & H16 & H47 & Hkh & Hac & Htop & Hhs).
pose proof w_nums as (HD0 & HDac & HM1 & HM2 & HN & HDcan & HDam & HP1 & HP2 & ACB).
assert (HSS : SNK_STK = 9104) by reflexivity.
pose proof (EK_2 E HK) as E2.
assert (HX : forall a, sp0 + FO <= a < sp0 + FO + 0xe8 -> vf_xw sp0 D M a) by (intros a Ha; left; unfold CKO; lia).
eapply SRr_bind; [exact (g_phase_to W E A_SNW vi3 ve4 RS_running ms md3 HS r_v4)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
change (st_ok tfibsegs E ve4 (restrict (w_H W) ms1)) in HS1.
pose proof (vf_after_run ly S U W mem md sp0 (vf_xw sp0 D M) E vi3 ve4 ms ms1 md3 mat1 w_base HX E2 vi3_win ve4_weq
  HS1 HF1 FI) as FI1.
set (md4 := with_vm_backing (m_vm_lazy md3) mat1 md3) in *.
assert (SNK1 : SNK W (ms_mem ms1) sp0 D N out b).
{ apply (SNK_same W (ms_mem ms) (ms_mem ms1)); [|exact HSNK]. intros x. apply HF1. exact (nowin E vi3 _ vi3_nowin). }
assert (Hb1 : snk_base B ly S U W (ms_mem ms1) md4 sp0).
{ apply (snk_base_frame B ly S U W mem md sp0 sp0 (vf_xw sp0 D M) _ _ w_base FI1); [lia | exact vf_xw_far]. }
pose proof (snk_dest_xfer ly S U W mem md (ms_mem ms1) md4 sp0 D M w_base w_dest FI1) as Hd1.
pose proof ve4_regs as (Q1 & Q2 & Q3 & Q4 & Q10 & Q11 & Q12).
pose proof (w_regs E ve4 ms1 RA_FLUSH HK HS1 Q1 ltac:(unfold RA_FLUSH; lia) eq_refl Q2 Q3 Q4) as Hregs1.
assert (R10 : getr (ms_regs ms1) 10 = w64 (sp0 + FO))
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS1), Q10, (EK_sp E 48 HK); reflexivity).
assert (R11 : getr (ms_regs ms1) 11 = w64 0) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS1), Q11; reflexivity).
assert (R12 : getr (ms_regs ms1) 12 = w64 0) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 12 HS1), Q12; reflexivity).
pose proof FI1 as (_ & _ & Hps1 & _).
eapply SRr_bind.
{ apply (vf_kcall ly S U W mem md sp0 (vf_xw sp0 D M) E ve4 ms1 md4 ve4_st [vwr; vf_can] 67 RA_FLUSH (-352) (-272)
    (fw_xw sp0 D M) (fw_xw sp0 D M) (sp0 + OSP_PC) 0 (fun m => SNK W m sp0 D N out 0) w_base FI1 HS1 E2 ve4_mem ve4_kok
    ltac:(unfold RA_FLUSH; lia)).
  - intros a Hx Ha. unfold fw_xw, IBO, CKO, FO in Hx. destruct Hx as [X|[X|[X|X]]]; lia.
  - intros a [Ha|Ha]; [left; unfold OSP_PC in Ha; lia | right; exact Ha].
  - intros a Hx. unfold fw_xw, IBO, CKO, FO in Hx. unfold vf_xw, dst_xw, CKO, FO.
    destruct Hx as [X|[X|[X|X]]]; [left; lia | right; left; lia | right; left; lia | right; right; exact X].
  - intros r a Hr Ha. destruct Hr as [<-|[<-|[]]]; unfold vwr, vf_can in Ha;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    + rewrite E2 in Ha. unfold FO in Ha. split; [lia|]. split; [lia|].
      unfold fw_xw, IBO, CKO, FO. intros [X|[X|[X|X]]]; lia.
    + unfold FM_canary in *. split; [lia|]. split; [unfold kHighMemBeg in *; lia|].
      unfold fw_xw, IBO, CKO, FO. intros [X|[X|[X|X]]]; lia.
  - intros r a Hr Ha. destruct Hr as [<-|[<-|[]]]; unfold vwr, vf_can in Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.
  - exact (AFLUSH ly S U W (ms_regs ms1) (ms_mem ms1) md4 sp0 D N M out b Hb1 Hregs1 R10 R11 R12 SNK1 Hd1
      ltac:(lia)). }
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & FI2 & H10 & HQ).
rewrite <- va4_eq in HS2.
set (E3 := havoc E 67 (map (getr (ms_regs ms2)) CLOB)) in *.
assert (HK3 : vEK E3) by (apply EK_havoc; [exact HK | lia]).
assert (E3_55 : ew E3 55 = w64 (Z.of_nat (length out))) by (subst E3; rewrite havoc_lt by lia; exact E55).
pose proof (EK_2 E3 HK3) as E32.
pose proof (st_ok_del E3 va4 _ [va4_st] vwr [vf_can] HS2 va4_mem) as HS2a.
pose proof FI2 as (_ & _ & Hp2 & _).
pose proof HQ as (S0 & S32 & S40 & _).
assert (HS2b : st_ok tfibsegs E3 vi4 (restrict (w_H W) ms2)).
{ apply (st_ok_ins E3 (set_mem va4 ([va4_st] ++ [vf_can])) _ [va4_st] vfl2 [vf_can] HS2a eq_refl (proj2 regions_wf_r)).
  - unfold region_ok, vfl2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32. split; [unfold FO; lia|]. split; [unfold FO; lia|]. split.
    + intros o Ho. apply apresent_writable. apply Hp2. unfold snk_band, FO in *. lia.
    + constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val tfibsegs E3 _ sp0 FO 4 (SLit 0) 0); [reflexivity | zside | zside | exact S0].
      * apply (chunk_ok_val tfibsegs E3 _ sp0 (FO + 40) 8 (SOff 2 IBO) (sp0 + IBO + 0)).
        -- rewrite (EK_sp E3 IBO HK3). unfold w64. f_equal. lia.
        -- unfold IBO; zside.
        -- zside.
        -- rewrite Z.add_assoc. exact S40.
  - apply (rdisj_all E3 sp0); [exact E32 | lia | exact (proj2 regions_r)]. }
exact (w_s5 ms2 _ E3 HK3 E3_55 HS2b FI2 HQ).
Qed.

(* printf_core (f, fmt, &ap2, nl_arg, nl_type), then the rest *)
Lemma w_s3 : forall ms md2 E, vEK E ->
  st_ok tfibsegs E ve3 (restrict (w_H W) ms) ->
  snk_frame B ly S U W mem md sp0 sp0 fxw (ms_mem ms) md2 ->
  SRr tfibsegs W (mkCfg ms md2) (gl_post B ly S U W regs mem md sp0 sp0 (vf_xw sp0 D M) D out).
Proof.
intros ms md2 E HK HS FI.
pose proof w_lay as (H44 & H16 & H47 & Hkh & Hac & Htop & Hhs).
pose proof w_nums as (HD0 & HDac & HM1 & HM2 & HN & HDcan & HDam & HP1 & HP2 & ACB).
assert (HSS : SNK_STK = 9104) by reflexivity.
pose proof (EK_2 E HK) as E2.
assert (E33 : ew E 33 = Z_to_bv 64 D) by exact (EK_x E 1 HK ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (N - 1)) by exact (EK_x E 2 HK ltac:(lia)).
pose proof (w_pre (ms_mem ms) md2 FI) as HPRE1.
pose proof HPRE1 as (Hb1 & Hrom1 & _ & Hin & Hfc1 & _ & _ & Hsl1 & Hfr1 & _ & _ & Hd1).
pose proof FI as (_ & _ & Hps & Hfr & _).
pose proof (snk_frame_weak ly S U W mem md sp0 sp0 fxw (vf_xw sp0 D M) (ms_mem ms) md2 FI
  ltac:(intros a Ha; left; exact Ha)) as FI'.
(* the sink as vfprintf hands it to printf_core: SNK [] 0 *)
assert (SL : forall off n e v, existsb (chunk_isn off n e) (YP09.r_chunks ve3_fl) = true -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 + off) (N.to_nat n) v).
{ intros off n e v Hc He Hv Hn. apply (slot_of W E ve3 ms 1 ve3_fl sp0 off n e v HS E2);
    [rewrite ve3_mem; reflexivity | exact (proj1 ve3_bases) | exact (chunk_isn_in off n e _ Hc) | exact He | exact Hv | exact Hn]. }
assert (DZ : aview tfibsegs (w_H W) (ms_mem ms) D = Some 0).
{ rewrite (Hfr D ltac:(lia) ltac:(lia) ltac:(unfold fxw, CKO, FO; lia)). exact (proj2 HVF). }
assert (SNK0 : SNK W (ms_mem ms) sp0 D N [] 0).
{ unfold SNK. cbv zeta. cbn [length Z.of_nat].
  split; [replace (sp0 + FO) with (sp0 + 48) by (unfold FO; lia);
    apply (SL 48 4%N (SLit 0)); [vm_compute; reflexivity | reflexivity | zside | zside]|].
  split; [replace (sp0 + FO + 32) with (sp0 + 80) by (unfold FO; lia);
    apply (SL 80 8%N (SOff 2 (-272))); [vm_compute; reflexivity | rewrite (EK_sp E _ HK); unfold w64, IBO; f_equal; lia
    | unfold IBO; zside | zside]|].
  split; [replace (sp0 + FO + 40) with (sp0 + 88) by (unfold FO; lia);
    apply (SL 88 8%N (SOff 2 (-352))); [vm_compute; reflexivity | rewrite (EK_sp E _ HK); unfold w64, IBO; f_equal; lia
    | unfold IBO; zside | zside]|].
  split; [replace (sp0 + FO + 56) with (sp0 + 104) by (unfold FO; lia);
    apply (SL 104 8%N (SOff 2 (-352))); [vm_compute; reflexivity | rewrite (EK_sp E _ HK); unfold w64, IBO; f_equal; lia
    | unfold IBO; zside | zside]|].
  split; [replace (sp0 + FO + 72) with (sp0 + 120) by (unfold FO; lia);
    apply (SL 120 8%N (SLit A_SNW)); [vm_compute; reflexivity | reflexivity | unfold A_SNW; zside | zside]|].
  split; [replace (sp0 + FO + 88) with (sp0 + 136) by (unfold FO; lia);
    apply (SL 136 8%N (SOff 2 (-352))); [vm_compute; reflexivity | rewrite (EK_sp E _ HK); unfold w64, IBO; f_equal; lia
    | unfold IBO; zside | zside]|].
  split; [replace (sp0 + FO + 144) with (sp0 + 192) by (unfold FO; lia);
    apply (SL 192 4%N (SLit 0xffffffff)); [vm_compute; reflexivity | reflexivity | zside | zside]|].
  split; [replace (sp0 + FO + 152) with (sp0 + 200) by (unfold FO; lia);
    apply (SL 200 8%N (SOff 2 280)); [vm_compute; reflexivity | rewrite (EK_sp E _ HK); unfold w64, CKO, FO; f_equal; lia
    | unfold CKO, FO; zside | zside]|].
  split; [replace (sp0 + CKO) with (sp0 + 280) by (unfold CKO, FO; lia);
    apply (SL 280 8%N (SOff 33 0)); [vm_compute; reflexivity
    | cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; lia | zside | zside]|].
  split; [replace (sp0 + CKO + 8) with (sp0 + 288) by (unfold CKO, FO; lia);
    apply (SL 288 8%N (SOff 34 0)); [vm_compute; reflexivity
    | cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; lia | zside | zside]|].
  split; [intros i Hi; lia|]. split; [intros i Hi; lia|].
  split; [match goal with |- aview _ _ _ (D + ?x) = _ => replace (D + x) with D by lia end; exact DZ|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | constructor]. }
(* the stack slot ap2 = P and the registers *)
pose proof ve3_regs as (Q1 & Q2 & Q3 & Q4 & Q10 & Q11 & Q12 & Q13 & Q14).
assert (Hap : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 + OSP_PC) 8 P).
{ apply (slot_of W E ve3 ms 0 ve3_st sp0 (-368) 8 (SOff 12 0) P HS E2);
    [rewrite ve3_mem; reflexivity | exact (proj2 ve3_bases) | apply chunk_isn_in; vm_compute; reflexivity | |
     unfold kHighMemEnd in *; zside | zside].
  rewrite (EK_reg E 12 12%bv HK ltac:(lia) eq_refl). exact G12. }
pose proof (w_regs E ve3 ms RA_PCORE HK HS Q1 ltac:(unfold RA_PCORE; lia) eq_refl Q2 Q3 Q4) as Hregs.
assert (R10 : getr (ms_regs ms) 10 = w64 (sp0 + FO))
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), Q10, (EK_sp E 48 HK); reflexivity).
assert (R11 : getr (ms_regs ms) 11 = w64 f)
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS), Q11, (EK_reg E 11 11%bv HK ltac:(lia) eq_refl); exact G11).
assert (R12 : getr (ms_regs ms) 12 = w64 (sp0 + OSP_PC))
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 12 HS), Q12, (EK_sp E _ HK); reflexivity).
assert (R13 : getr (ms_regs ms) 13 = w64 (sp0 + OSP_PC + 0x60))
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 13 HS), Q13, (EK_sp E _ HK); unfold w64, OSP_PC; f_equal; lia).
assert (R14 : getr (ms_regs ms) 14 = w64 (sp0 + OSP_PC + 0x108))
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 14 HS), Q14, (EK_sp E _ HK); unfold w64, OSP_PC; f_equal; lia).
(* drop the FILE (the sink writes wpos / wbase) and the GOT cell *)
pose proof (st_ok_del E ve3 _ [ve3_st] ve3_fl [vf_got; vf_can] HS ve3_mem) as HSa.
pose proof (st_ok_del E (set_mem ve3 ([ve3_st] ++ [vf_got; vf_can])) _ [ve3_st] vf_got [vf_can] HSa eq_refl) as HSb.
change (st_ok tfibsegs E (set_mem ve3 [ve3_st; vf_can]) (restrict (w_H W) ms)) in HSb.
eapply SRr_bind.
{ apply (vf_kcall ly S U W mem md sp0 (vf_xw sp0 D M) E (set_mem ve3 [ve3_st; vf_can]) ms md2 ve3_st [vf_can] 51
    RA_PCORE (-368) (-272) (fun a => sp0 - 368 <= a < sp0 - 360 \/ fw_xw sp0 D M a) (fw_xw sp0 D M)
    (sp0 + OSP_PC + 8) (Z.of_nat (length out)) (fun m => exists b', SNK W m sp0 D N out b')
    w_base FI' HSb E2 eq_refl ve3_kok ltac:(unfold RA_PCORE; lia)).
  - intros a Hx Ha. unfold fw_xw, IBO, CKO, FO in Hx. destruct Hx as [X|[X|[X|[X|X]]]]; lia.
  - intros a [Ha|Ha]; [|right; right; exact Ha]. unfold OSP_PC in Ha.
    destruct (Z_lt_le_dec a (sp0 - 368)); [left; lia | right; left; lia].
  - intros a [X|X]; [left; lia|]. unfold fw_xw, IBO, CKO, FO in X. unfold vf_xw, dst_xw, CKO, FO.
    destruct X as [X|[X|[X|X]]]; [left; lia | right; left; lia | right; left; lia | right; right; exact X].
  - intros r a Hr Ha. destruct Hr as [<-|[]]. unfold vf_can in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    unfold FM_canary in *. split; [lia|]. split; [unfold kHighMemBeg in *; lia|].
    unfold fw_xw, IBO, CKO, FO. intros [X|[X|[X|[X|X]]]]; lia.
  - intros r a Hr Ha. destruct Hr as [<-|[]]. unfold vf_can in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
  - exact (APCORE ly S U W (ms_regs ms) (ms_mem ms) md2 sp0 D N M f ps P args out Hb1 Hregs Hrom1 R10 R11 R12 R13 R14
      Hin Hfc1 Hap HP1 HP2 Hsl1 Hfr1 ltac:(lia) SNK0 Hd1). }
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & FI2 & H10 & (b' & HQ)).
rewrite <- va3_eq in HS2.
set (E2' := havoc E 51 (map (getr (ms_regs ms2)) CLOB)) in *.
assert (HK2 : vEK E2') by (apply EK_havoc; [exact HK | lia]).
assert (E55 : ew E2' 55 = w64 (Z.of_nat (length out))) by exact H10.
pose proof (EK_2 E2' HK2) as E22.
(* the stack window closes (nothing below sp0 is stored any more), f->write becomes readable *)
pose proof (st_ok_win0 E2' va3 _ va3_st [vf_can] HS2 va3_mem) as HS2a.
pose proof HQ as (_ & _ & _ & _ & S72 & _).
assert (HS2b : st_ok tfibsegs E2' vi3 (restrict (w_H W) ms2)).
{ apply (st_ok_ins E2' (set_mem va3 [win0 va3_st; vf_can]) _ [win0 va3_st] vwr [vf_can] HS2a eq_refl (proj1 regions_wf_r)).
  - unfold region_ok, vwr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E22. split; [unfold FO; lia|]. split; [unfold FO; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs E2' _ sp0 (FO + 72) 8 (SLit A_SNW) A_SNW);
      [reflexivity | unfold A_SNW; zside | zside | rewrite Z.add_assoc; exact S72].
  - apply (rdisj_all E2' sp0); [exact E22 | lia | exact (proj1 regions_r)]. }
exact (w_s4 ms2 _ E2' b' HK2 E55 HS2b FI2 HQ).
Qed.

(* printf_core (0, ..) returned 0: the branch, the FILE set up, then printf_core (f, ..) *)
Lemma w_s2 : forall ms md1 E, vEK E -> ew E 39 = w64 0 ->
  st_ok tfibsegs E va1 (restrict (w_H W) ms) ->
  snk_frame B ly S U W mem md sp0 sp0 fxw (ms_mem ms) md1 ->
  SRr tfibsegs W (mkCfg ms md1) (gl_post B ly S U W regs mem md sp0 sp0 (vf_xw sp0 D M) D out).
Proof.
intros ms md1 E HK E39 HS FI.
pose proof (EK_2 E HK) as E2.
assert (HX : forall a, sp0 + FO <= a < sp0 + FO + 0xe8 -> fxw a) by (intros a Ha; unfold fxw, CKO; lia).
eapply SRr_bind; [exact (g_phase_to W E A_PCORE va1 ve2 _ ms md1 HS r_v2)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
change (st_ok tfibsegs E ve2 (restrict (w_H W) ms1)) in HS1.
pose proof (vf_after_run ly S U W mem md sp0 fxw E va1 ve2 ms ms1 md1 mat1 w_base HX E2 va1_win ve2_weq HS1 HF1 FI) as FI1.
assert (Hbr : branch_taken BC_LT (sv_denot E (SOff 39 0)) (sv_denot E (SLit 0)) = false).
{ cbn [sv_denot]. rewrite E39. vm_compute. reflexivity. }
pose proof (st_ok_add_cond_neg tfibsegs E ve2 _ BC_LT (SOff 39 0) (SLit 0) HS1 Hbr) as HS1'.
rewrite <- vc2_eq in HS1'.
eapply SRr_bind; [exact (g_phase_to W E A_PCORE vc2 ve3 _ ms1 _ HS1' r_v3)|].
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2).
change (st_ok tfibsegs E ve3 (restrict (w_H W) ms2)) in HS2.
pose proof (vf_after_run ly S U W mem md sp0 fxw E vc2 ve3 ms1 ms2 _ mat2 w_base HX E2 vc2_win ve3_weq HS2 HF2 FI1) as FI2.
exact (w_s3 ms2 _ E HK HS2 FI2).
Qed.

(* entry (AE3h.v vf_entry on vsnprintf's FILE) *)
Lemma w_entry : st_ok tfibsegs vE0 vs0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_VFP) mem (seg_rom tfibsegs))).
Proof.
pose proof w_lay as (H44 & H16 & H47 & Hkh & Hac & Htop & Hhs).
pose proof w_nums as (HD0 & HDac & HM1 & HM2 & HN & HDcan & HDam & HP1 & HP2 & ACB).
pose proof w_base as (_ & _ & _ & _ & _ & _ & _ & _ & Hband & _).
pose proof HPRE as (_ & _ & (cv' & Hgot & _ & _) & _).
pose proof HVF as (HF & _).
assert (HSS : SNK_STK = 9104) by reflexivity.
pose proof E0_2 as E2.
assert (E32 : ew vE0 32 = Z_to_bv 64 cval) by exact (ew_Ereg_extra regs _ 0).
assert (E33 : ew vE0 33 = Z_to_bv 64 D) by exact (ew_Ereg_extra regs _ 1).
assert (E34 : ew vE0 34 = Z_to_bv 64 (N - 1)) by exact (ew_Ereg_extra regs _ 2).
rewrite restrict_mkst_fx. unfold vs0.
apply (entry_st_ok_full tfibsegs A_VFP vf_sr0 regs [Z_to_bv 64 cval; Z_to_bv 64 D; Z_to_bv 64 (N - 1)]);
  change (Ereg regs [Z_to_bv 64 cval; Z_to_bv 64 D; Z_to_bv 64 (N - 1)]) with vE0.
- unfold vf_sr0. apply regs_ok_pin; [unfold vE0; apply regs_ok_Ereg | intros Hx; discriminate Hx |].
  rewrite G10, (EK_sp vE0 FO EK_0). reflexivity.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + unfold vf_stk0, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply apresent_writable; apply Hband; unfold snk_band; lia | constructor].
  + unfold vf_fil0, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [unfold FO; lia|]. split; [unfold CKO, FO; lia|].
    split; [intros o Ho; apply apresent_writable; apply Hband; unfold snk_band, FO in *; lia|].
    unfold vf_file_chunks, vfz. unfold vsn_fields in HF.
    repeat match type of HF with Forall _ (_ :: _) =>
      let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbv beta in h; cbn [fst snd] in h;
      apply Forall_inv_tail in HF end.
    repeat apply Forall_cons; try apply Forall_nil;
    (eapply (chunk_ok_val tfibsegs vE0 _ sp0); [ | | | rewrite Z.add_assoc; eassumption ]);
    first [ reflexivity
          | (rewrite (EK_sp vE0 _ EK_0); unfold w64; f_equal; lia)
          | (cbn [sv_denot]; first [rewrite E33 | rewrite E34]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          | (unfold CKO, FO, A_SNW; zside) ].
  + unfold vf_got, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold FM_GOT_canary; lia|]. split; [unfold FM_GOT_canary; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. eapply (chunk_ok_val tfibsegs vE0 _ 0); [reflexivity | unfold FM_canary; zside | zside |].
    rewrite Z.add_0_l. exact Hgot.
  + unfold vf_can, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold FM_canary; lia|]. split; [unfold FM_canary; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. eapply (chunk_ok_val tfibsegs vE0 _ 0 _ 8 _ cval);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_l. exact HCAN.
- apply pairwise_disjoint_of_extents. unfold vf_stk0, vf_fil0, vf_got, vf_can, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  unfold CKO, FO, FM_GOT_canary, FM_canary. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; exact I]. cbn [vf_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16. repeat split; lia.
Qed.

(* prologue, printf_core (0, fmt, &ap2, nl_arg, nl_type), then the rest *)
Lemma w_s1 : SRr tfibsegs W (cfg_at tfibsegs A_VFP regs mem md)
  (gl_post B ly S U W regs mem md sp0 sp0 (vf_xw sp0 D M) D out).
Proof.
pose proof w_lay as (H44 & H16 & H47 & Hkh & Hac & Htop & Hhs).
pose proof w_nums as (HD0 & HDac & HM1 & HM2 & HN & HDcan & HDam & HP1 & HP2 & ACB).
assert (HSS : SNK_STK = 9104) by reflexivity.
pose proof E0_2 as E2.
assert (HX : forall a, sp0 + FO <= a < sp0 + FO + 0xe8 -> fxw a) by (intros a Ha; unfold fxw, CKO; lia).
pose proof (g_frame_init B ly S U W mem md sp0 sp0 fxw w_base ltac:(lia)) as FI0.
unfold cfg_at. change (w64 A_VFP) with (Z_to_bv 64 A_VFP).
eapply SRr_bind; [exact (g_phase_to W vE0 A_PCORE vs0 ve1 RS_running _ md w_entry r_v1)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
change (st_ok tfibsegs vE0 ve1 (restrict (w_H W) ms1)) in HS1.
pose proof (vf_after_run ly S U W mem md sp0 fxw vE0 vs0 ve1 (mkst regs (Z_to_bv 64 A_VFP) mem (seg_rom tfibsegs)) ms1 md
  mat1 w_base HX E2 vs0_win ve1_weq HS1 HF1 FI0) as FI1.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
pose proof (w_pre (ms_mem ms1) md1 FI1) as HPRE1.
pose proof HPRE1 as (Hb1 & Hrom1 & _ & Hin & _).
pose proof FI1 as (_ & _ & Hps & _).
pose proof ve1_r12 as (Q1 & Q2).
pose proof ve1_regs as (Q3 & Q4 & Q10 & Q11 & Q12 & Q13 & Q14).
pose proof (w_regs vE0 ve1 ms1 RA_PCORE0 EK_0 HS1 Q1 ltac:(unfold RA_PCORE0; lia) eq_refl Q2 Q3 Q4) as Hregs.
assert (R10 : getr (ms_regs ms1) 10 = w64 0) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) vE0 _ _ 10 HS1), Q10; reflexivity).
assert (R11 : getr (ms_regs ms1) 11 = w64 f)
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) vE0 _ _ 11 HS1), Q11, (EK_reg vE0 11 11%bv EK_0 ltac:(lia) eq_refl); exact G11).
assert (R12 : getr (ms_regs ms1) 12 = w64 (sp0 + OSP_PC))
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) vE0 _ _ 12 HS1), Q12, (EK_sp vE0 _ EK_0); reflexivity).
assert (R13 : getr (ms_regs ms1) 13 = w64 (sp0 + OSP_PC + 0x60))
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) vE0 _ _ 13 HS1), Q13, (EK_sp vE0 _ EK_0); unfold w64, OSP_PC; f_equal; lia).
assert (R14 : getr (ms_regs ms1) 14 = w64 (sp0 + OSP_PC + 0x108))
  by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) vE0 _ _ 14 HS1), Q14, (EK_sp vE0 _ EK_0); unfold w64, OSP_PC; f_equal; lia).
eapply SRr_bind.
{ apply (vf_kcall ly S U W mem md sp0 fxw vE0 ve1 ms1 md1 ve1_st [vf_fil0; vf_got; vf_can] 35 RA_PCORE0 0 0
    (fun _ => False) (fun _ => False) (sp0 + OSP_PC) 0 (fun _ => True) w_base FI1 HS1 E2 ve1_mem ve1_kok
    ltac:(unfold RA_PCORE0; lia)).
  - intros a [].
  - intros a [Ha|[]]. left. unfold OSP_PC in Ha. lia.
  - intros a [].
  - intros r a Hr Ha. destruct Hr as [<-|[<-|[<-|[]]]]; unfold vf_fil0, vf_got, vf_can in Ha;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    + rewrite E2 in Ha. unfold CKO, FO in Ha. split; [lia|]. split; [lia | intros X; exact X].
    + unfold FM_GOT_canary in Ha. split; [lia|]. split; [unfold kHighMemBeg in *; lia | intros X; exact X].
    + unfold FM_canary in Ha. split; [lia|]. split; [unfold kHighMemBeg in *; lia | intros X; exact X].
  - intros r a Hr Ha. destruct Hr as [<-|[<-|[<-|[]]]]; unfold vf_fil0, vf_got, vf_can in Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    + rewrite E2 in Ha. apply Hps. unfold snk_band, FO in *. lia.
    + lia.
    + lia.
  - exact (APCORE0 ly S U W (ms_regs ms1) (ms_mem ms1) md1 sp0 f ps Hb1 Hregs Hrom1 R10 R11 R12 R13 R14 Hin). }
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & FI2 & H10 & _).
rewrite <- va1_eq in HS2.
exact (w_s2 ms2 _ (havoc vE0 35 (map (getr (ms_regs ms2)) CLOB)) (EK_havoc vE0 35 _ EK_0 ltac:(lia)) H10 HS2 FI2).
Qed.
End w.

Theorem avfp_ok : avfp_realizes B A_VFP.
Proof.
intros ly S U W regs mem md sp0 D N M f ps P args out HPRE HREG G10 G11 G12 HVF.
pose proof HPRE as (_ & _ & (cval & _ & Hcan & Hcv) & _).
eapply w_s1; eassumption.
Qed.
End v.
