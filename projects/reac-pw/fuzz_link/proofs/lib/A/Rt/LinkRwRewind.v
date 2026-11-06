(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AE23.v, with its module paths changed; 658 of its 722 lines of code are new or changed and 1611 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build fuzz_link.asan, pin 059dae63e07c): rewind(f) on link's memory FILE,
   LinkMfDefs.v's arewind_mf_realizes, proved at its three entries.

   - link_arewind_musl, musl rewind 0x97210 (frame 32):
     +0x00..+0x10  push 32, save ra, s0, s1; s0 = a0 = f;
     +0x14 lw a0,0x8c(a0)  the FILE's lock word at f + 140, which amemfile_static fixes to 0xffffffff, read signed;
     +0x18 bltz a0         taken (-1 < 0), so __lockfile 0x9648c and __unlockfile 0x96588 are not reached;
     +0x60..+0x6c          a0 = f, a1 = 0, a2 = 0; jal __fseeko_unlocked 0x96e78: the Section hypothesis HFS
                           (LinkRwDefs.v afseeko0_mf_realizes) at sp - 32 (ARW_STK = 32 + AFS_STK);
     +0x70..+0x78          lwu, andi -0x21, sw: the flags word loses F_ERR. After the call it is 4 or 36
                           (amemfile_flags of the call's amf_k); both give 4 = AF_NORD;
     +0x7c..+0x8c          restore ra, s0, s1; pop 32; ret.
   - link_arewind_icpt, ___interceptor_rewind 0x48ce8 (frame 16): +0x10 jal TryAsanInitFromRtl 0x5b214 (frame 16),
     whose lb at 0xab118 reads 1 (AR's constant table row z1 (ANum 0xab118) 0x1), so +0x20 bne is not taken and it
     returns at +0x30 (its lr.w / sc.w loop and jal 0x5af60 are not reached); +0x14 / +0x18 t1 = the word at
     0xa37d8 (AR's constant table row z8 (ANum 0xa37d8) 0x97210); +0x1c..+0x28 a0 = f, restore ra and s0, pop 16;
     +0x2c jr t1: musl rewind at the caller's sp and ra, with a1 = 1 and t1 changed, so link_arewind_musl applies
     there.
   - link_arewind_mf_ok: the trampoline 0x430d4, j 0x48ce8.

   Each walk runs the frame's symbolic engine (the method of lib/A/AE2t.v, AE2y.v, AE36.v) over rw_tbl, a code table of exactly these instructions
   (lib/A/AE34.v build_ranges). Listings of image A: link-a/listings/runtime/{wrapper_rewind.jump,wrapper_rewind,rt_0,rewind}.fuzz_link.asan.s
   (internal records, sha256 3e83d0142ec8, 7dd0e084a483, 8efa0ced8b02 and 08b36455316c). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac zof := repeat match goal with |- context [Z.of_nat ?n] =>
  let v := eval vm_compute in (Z.of_nat n) in
  lazymatch v with Z.of_nat _ => fail | _ => change (Z.of_nat n) with v end end.

(* ==========================================================================
   1. The FILE's words across a change of memory
   ========================================================================== *)

Section c.
Variable segs : list Segment.
Variable MS : amemfile_syms.

(* every word the path's FILE predicates read lies in the FILE's block *)
Lemma amf_move : forall (m m' : word -> option byte) f k fl om wend wpos wbase pos len pb,
  (forall x, f <= x < f + AMF_BLOCK -> mbyte segs m' x = mbyte segs m x) ->
  amf_k segs MS m f k -> amf_dyn segs MS m f fl om wend wpos wbase pos len -> amf_pend segs m f pb ->
  Z.of_nat (length pb) = k ->
  amf_k segs MS m' f k /\ amf_dyn segs MS m' f fl om wend wpos wbase pos len /\ amf_pend segs m' f pb.
Proof.
intros m m' f k fl om wend wpos wbase pos len pb Hfr [Hat Hwin] Hdyn Hpend Hlen.
assert (HV : forall off n v, 0 <= off -> off + Z.of_nat n <= AMF_BLOCK ->
  val_mem segs m (f + off) n v -> val_mem segs m' (f + off) n v).
{ intros off n v H0 H1 Hv. eapply amf_val_mem_frame; [|exact Hv]. intros x Hx. apply Hfr. lia. }
assert (Hk : 0 <= k <= AMF_BUFSIZ) by (destruct Hwin as [(-> & _) | (H & _)]; unfold AMF_BUFSIZ in *; lia).
split; [split|split].
- apply (amemfile_at_frame segs MS m m' f); [|exact Hat].
  intros x Hx. apply Hfr. unfold AMF_ZEROED, AMF_BLOCK in *. lia.
- unfold amf_win in *. destruct Hwin as [(H0 & H1 & H2 & H3) | (H0 & H1 & H2 & H3)]; [left | right];
  (split; [exact H0|]); (split; [|split]); (apply HV; [lia | zof; unfold AMF_BLOCK; lia | assumption]).
- unfold amf_dyn in *. destruct Hdyn as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & V1 & V2 & V3 & V4 & V5 & V6 & V7).
  do 7 (split; [assumption|]).
  repeat match goal with |- _ /\ _ => split end;
  (apply HV; [unfold AMF_COOKIE; lia | zof; unfold AMF_COOKIE, AMF_BLOCK; lia | assumption]).
- unfold amf_pend, azbytes, amf_rd in *. intros i Hi. rewrite Hfr; [exact (Hpend i Hi)|].
  unfold AMF_BUF, AMF_BLOCK, AMF_BUFSIZ in *. lia.
Qed.

Lemma amf_static_frame4 : forall (m m' : word -> option byte) f,
  (forall x, f + 4 <= x < f + AMF_BLOCK -> mbyte segs m' x = mbyte segs m x) ->
  amemfile_static segs MS m f -> amemfile_static segs MS m' f.
Proof.
intros m m' f Hfr Hs.
assert (HV : forall off n v, 4 <= off -> off + Z.of_nat n <= AMF_BLOCK ->
  val_mem segs m (f + off) n v -> val_mem segs m' (f + off) n v).
{ intros off n v H0 H1 Hv. eapply amf_val_mem_frame; [|exact Hv]. intros x Hx. apply Hfr. lia. }
clear Hfr. unfold amemfile_static, AMF_COOKIE in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat match goal with |- _ /\ _ => split end; (apply HV; [lia | zof; unfold AMF_BLOCK; lia | assumption]).
Qed.

(* the store at +0x78 changes only the flags word [f, f + 4) and writes F_NORD there *)
Lemma amf_flags_set : forall (m m' : word -> option byte) f k fl om wend wpos wbase pos len,
  (forall x, f + 4 <= x < f + AMF_BLOCK -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m' f 4 AF_NORD ->
  amf_k segs MS m f k -> amf_dyn segs MS m f fl om wend wpos wbase pos len ->
  amf_k segs MS m' f k /\ amf_dyn segs MS m' f AF_NORD om wend wpos wbase pos len.
Proof.
intros m m' f k fl om wend wpos wbase pos len Hfr Hfl [(Hf0 & Hf1 & Hf2 & Hs & _ & Hom & Hw & Hc) Hwin] Hdyn.
assert (HV : forall off n v, 4 <= off -> off + Z.of_nat n <= AMF_BLOCK ->
  val_mem segs m (f + off) n v -> val_mem segs m' (f + off) n v).
{ intros off n v H0 H1 Hv. eapply amf_val_mem_frame; [|exact Hv]. intros x Hx. apply Hfr. lia. }
assert (HF0 : val_mem segs m' (f + 0) 4 AF_NORD) by (rewrite Z.add_0_r; exact Hfl).
split; [split|].
- split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Hf2|].
  split; [exact (amf_static_frame4 m m' f Hfr Hs)|].
  split; [left; exact HF0|].
  split; [destruct Hom as [H|H]; [left|right]; (apply HV; [lia | zof; unfold AMF_BLOCK; lia | exact H])|].
  split.
  + destruct Hw as (H8 & H16 & [(H1 & H2 & H3) | (kk & Hkk & H1 & H2 & H3)]);
    (split; [apply HV; [lia | zof; unfold AMF_BLOCK; lia | exact H8]|]);
    (split; [apply HV; [lia | zof; unfold AMF_BLOCK; lia | exact H16]|]).
    * left. split; [|split]; (apply HV; [lia | zof; unfold AMF_BLOCK; lia | assumption]).
    * right. exists kk. split; [exact Hkk|]. split; [|split]; (apply HV; [lia | zof; unfold AMF_BLOCK; lia | assumption]).
  + destruct Hc as (p & l & Hp & Hl & H1 & H2). exists p, l. split; [exact Hp|]. split; [exact Hl|].
    split; (apply HV; [unfold AMF_COOKIE; lia | zof; unfold AMF_COOKIE, AMF_BLOCK; lia | assumption]).
- unfold amf_win in *. destruct Hwin as [(H0 & H1 & H2 & H3) | (H0 & H1 & H2 & H3)]; [left | right];
  (split; [exact H0|]); (split; [|split]); (apply HV; [lia | zof; unfold AMF_BLOCK; lia | assumption]).
- unfold amf_dyn in *. destruct Hdyn as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & V1 & V2 & V3 & V4 & V5 & V6 & V7).
  split; [unfold AF_NORD; lia|]. do 6 (split; [assumption|]). split; [exact HF0|].
  repeat match goal with |- _ /\ _ => split end;
  (apply HV; [unfold AMF_COOKIE; lia | zof; unfold AMF_COOKIE, AMF_BLOCK; lia | assumption]).
Qed.

Lemma azbytes_move : forall (m m' : word -> option byte) a l,
  (forall i, (i < length l)%nat -> mbyte segs m' (a + Z.of_nat i) = mbyte segs m (a + Z.of_nat i)) ->
  azbytes segs m a l -> azbytes segs m' a l.
Proof. intros m m' a l Hfr H i Hi. unfold amf_rd. rewrite Hfr by exact Hi. exact (H i Hi). Qed.

End c.

Lemma rdword_ext : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (rewrite <- (Z.add_0_r a); apply H; lia).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* g_said lies in the image (the segment 0xa3000 .. 0x652000) *)
Lemma said_img : forall a, 0x62fee0 <= a < 0x62fee0 + 4096 -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (Hx : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x62fee0) &&
  (0x62fee0 + 4096 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ==========================================================================
   2. The code table and the symbolic runs
   ========================================================================== *)

(* each count is the function's size in link's .symtab over 4 (link-a/facts/syms.tsv (internal record, sha256 4def0c9bfebf):
   __interceptor_trampoline_rewind 4 B, ___interceptor_rewind 48 B, TryAsanInitFromRtl 160 B, rewind 144 B) *)
Definition rw_ranges : list (Z * nat) := [(0x430d4, 1%nat); (0x48ce8, 12%nat); (0x5b214, 40%nat); (0x97210, 36%nat)].
Definition rw_tbl : ctable := Eval vm_compute in build_ranges rw_ranges TEmpty.
Lemma rw_tbl_eq : rw_tbl = build_ranges rw_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl rw_tbl). Qed.
Lemma rw_tbl_ok : table_ok tfibsegs rw_tbl.
Proof.
rewrite rw_tbl_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold rw_ranges. repeat constructor; cbn; discriminate.
Qed.

Lemma rw_run_to : forall (W : world tfibsegs) E stop ss ss' ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs rw_tbl FUEL stop ss = (ss', RS_running) ->
  SRr tfibsegs W (mkCfg ms md)
  (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
   st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
   frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs rw_tbl rw_tbl_ok AF0x.Hwx_tfa W FUEL stop E ss ss' RS_running ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

Lemma rw_run : forall (W : world tfibsegs) E ss ss' why ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs rw_tbl FUEL ss = (ss', RS_stopped why) ->
  SRr tfibsegs W (mkCfg ms md)
  (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
   st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
   frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' why ms md HS Hrun.
eapply (SRr_run_gen tfibsegs rw_tbl rw_tbl_ok AF0x.Hwx_tfa W FUEL E ss ss' (RS_stopped why) ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

(* the two rows of AR's constant table the wrapper reads: asan_inited (TryAsanInitFromRtl +0x14) and REAL(rewind)
   (___interceptor_rewind +0x18) *)
Definition rw_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
  [(0xab118, 1, [(0, 1%N, 1)]); (0xa37d8, 8, [(0, 8%N, 0x97210)])].
Lemma rw_rodata_chk : forall ly, rodata_chk ly rw_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

(* the wrapper, from the trampoline or from its own entry, up to musl rewind's entry *)
Definition R_stkI : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition ssI (pc : Z) : sstate :=
  mkSS pc sr_atoms (R_stkI :: map ro_region rw_rodata) None (mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4)] [] []).
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs rw_tbl FUEL stop s.
Definition eI : sstate := Eval vm_compute in fst (RUNTO LA_REWIND (ssI LA_I_REWIND)).
Lemma r_II : RUNTO LA_REWIND (ssI LA_I_REWIND) = (eI, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma r_IW : RUNTO LA_REWIND (ssI LA_W_REWIND) = (eI, RS_running). Proof. vm_compute. reflexivity. Qed.

(* musl rewind up to the call of __fseeko_unlocked *)
Definition R_stkM : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition R_lock : YP09.region :=
  YP09.mkRegion (Some 10%nat) 140 144 140 140 [YP09.mkChunk 140 (CVal 4 (SLit 0xffffffff))].
Definition ssM : sstate :=
  mkSS LA_REWIND sr_atoms [R_stkM; R_lock] None
    (mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 4)] [] []).
Definition eM : sstate := Eval vm_compute in fst (RUNTO LA_FSEEKO ssM).
Lemma r_M : RUNTO LA_FSEEKO ssM = (eM, RS_running). Proof. vm_compute. reflexivity. Qed.

(* musl rewind from the return of __fseeko_unlocked (+0x70) to its ret (+0x8c); the atoms 32, 33, 34 are the
   caller's ra, s0, s1 that the prologue saved, the flags word holds fl *)
Definition RA_FS : Z := 0x97280.
Definition R_stkE : YP09.region :=
  YP09.mkRegion (Some 2%nat) 8 32 8 8
    [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
Definition R_flE (fl : Z) : YP09.region := YP09.mkRegion (Some 8%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SLit fl))].
Definition ssE (fl : Z) : sstate :=
  mkSS RA_FS sr_atoms [R_stkE; R_flE fl] None (mkFacts [(2%nat, mkAF (2 ^ 43) (2 ^ 47) 4)] [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs rw_tbl FUEL s.
Definition eE : sstate := Eval vm_compute in fst (RUN (ssE AF_NORD)).
Lemma r_E4 : RUN (ssE 4) = (eE, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_E36 : RUN (ssE 36) = (eE, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.

(* registers the code never writes, as atoms of the entry *)
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (s : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG s r) v.
Definition KEPTR : list Z := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition kept_ok (s : sstate) : bool := forallb (fun r => reg_is s r (SOff (Z.to_nat r) 0)) KEPTR.
Lemma kept_eM : kept_ok eM = true. Proof. vm_compute. reflexivity. Qed.
Lemma kept_eE : kept_ok eE = true. Proof. vm_compute. reflexivity. Qed.

Lemma kept_regs : forall H E ss ms regs0 extra,
  st_ok tfibsegs E ss (restrict H ms) -> E = Ereg regs0 extra -> kept_ok ss = true ->
  forall r, In r KEPTR -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros H E ss ms regs0 extra HS HE Hk r Hr. unfold kept_ok in Hk. rewrite forallb_forall in Hk.
specialize (Hk r Hr). unfold reg_is, RG in Hk. apply sv_eqb_eq in Hk.
assert (Hr32 : 0 <= r < 32) by (cbv [KEPTR In] in Hr; lia).
rewrite (st_ok_reg_denot H E ss ms _ HS), Hk. subst E. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply ew_Ereg_nat. rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma acs_kept : forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> In r KEPTR.
Proof. intros r Hr H2 H8 H9. unfold acallee_saved in Hr. cbv [KEPTR In]. lia. Qed.

Lemma ap_lit : forall regs regs' (r : bv 5) (z : Z),
  aregs_preserved regs regs' -> acallee_saved z -> bv_unsigned r = z -> getr regs' r = getr regs r.
Proof.
intros regs regs' r z H Hz Hr. subst z. pose proof (H _ Hz) as X. rewrite !Z_to_bv_bv_unsigned in X. exact X.
Qed.

Lemma chunk_val_nth : forall H E ss ms (i j : nat) r off (n : N) e v,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros H E ss ms i j r off n e v HS Hr Hc He Hv Hn.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hr)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hc)) as Hck.
exact (val_of_chunk_ok tfibsegs E _ _ off n e v Hck He Hv Hn).
Qed.

Lemma window_writable : forall H E ss ms (i : nat) r a,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
  writable_at tfibsegs (mrestrict H (ms_mem ms)) a.
Proof.
intros H E ss ms i r a HS Hr Ha.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hr)) as (_ & _ & Hw & _).
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.

(* from StrnlenMusl.v (this unit): a writable byte outside the image is present *)
Lemma apresent_of_writable : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  writable_at tfibsegs (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hn Hw. unfold apresent. unfold writable_at, wview, mrestrict in Hw.
rewrite unsigned_lit_small in Hw by lia. rewrite (find_segment_none a Hn) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:E; try rewrite E in Hw; [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|].
try rewrite Eb in Hw. exfalso. apply Hw. reflexivity.
Qed.

Lemma pres_move : forall (H : word -> bool) (mem mem1 : word -> option byte) lo hi,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem1 x = mem x) ->
  (forall a, lo <= a < hi -> apresent H mem1 a) ->
  forall a, apresent H mem a -> apresent H mem1 a.
Proof.
intros H mem mem1 lo hi MEQ P1 a Hp. rewrite (apresent_mod H mem1 a). rewrite (apresent_mod H mem a) in Hp.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' lo) as [L1|L1].
- apply (apresent_same H mem mem1 a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hp].
- destruct (Z_lt_le_dec a' hi) as [L2|L2]; [apply P1; lia|].
  apply (apresent_same H mem mem1 a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hp].
Qed.

(* ==========================================================================
   3. AR and the buffer's premises across a write to a window AR does not own
   ========================================================================== *)

Section S.
Variable B : asyms.
Hypothesis TB : PcapSyms B.

Lemma AR_win_move : forall ly S (W : world tfibsegs) mem md mem1 md1 lo hi,
  AR tfibsegs B ly S W mem md ->
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> ~ aowned B ly S a) ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem1 x = mem x) ->
  (forall a, lo <= a < hi -> apresent (w_H W) mem1 a) ->
  (forall a, lo <= a < hi -> apresent (w_H W) mem a) ->
  same_but_materialized md md1 ->
  AR tfibsegs B ly S W mem1 md1.
Proof.
intros ly S W mem md mem1 md1 lo hi HAR Hlo Hhi Hown MEQ P1 P0 Hsbm.
pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
pose proof (same_but_materialized_frame md md1 Hsbm) as MF.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Hn. }
apply (al_frame _ _ LAWS ly S W mem md mem1 md1 HAR).
- intros a Ha Hw. apply AV; [exact Ha|]. intros Hin. exact (Hown a Hin Hw).
- intros a Hv. rewrite (aview_mod _ mem1 a). rewrite (aview_mod _ mem a) in Hv.
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  destruct (Z_lt_le_dec (a mod 2 ^ 64) lo) as [L1|L1]; [rewrite AV by lia; exact Hv|].
  destruct (Z_lt_le_dec (a mod 2 ^ 64) hi) as [L2|L2]; [apply aview_some_of_apresent; apply P1; lia|].
  rewrite AV by lia. exact Hv.
- apply MF.
- apply MF.
- apply MF.
- exact (hs_kept_win _ _ _ _ _ _ _ _ MEQ P0 ltac:(lia) ltac:(lia)).
Qed.

Lemma amf_buf_ok_move : forall MS K K' ly S (W : world tfibsegs) regs regs' mem mem',
  amf_buf_ok tfibsegs B MS K ly S W regs mem ->
  spZ regs - K <= spZ regs' - K' -> spZ regs' <= spZ regs -> kHighMemBeg <= spZ regs - K ->
  (forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) ->
     mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  amf_buf_ok tfibsegs B MS K' ly S W regs' mem'.
Proof.
intros MS K K' ly S W regs regs' mem mem' (H0 & H1 & H2 & Hb & Hamr & Hra & Hhull) Hw1 Hw2 Hhi Hfr.
pose proof (u64_range (getr regs 2)) as Hsp. change (bv_unsigned (getr regs 2)) with (spZ regs) in Hsp.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
  aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. apply aview_eq_of. apply Hfr. rewrite unsigned_lit_small by lia. exact Hn. }
assert (HB : amf_buf MS + amf_size MS <= kHighMemEnd) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (SH : forall y, 0 <= y < kHighMemEnd -> 0 <= shadow_addr y /\ shadow_addr y / 8 * 8 + 8 <= spZ regs - K /\
  shadow_addr y / 8 * 8 + 8 <= 2 ^ 47).
{ intros y Hy. pose proof (shadow_addr_bounds y Hy) as [B1 B2].
  pose proof (Z.div_mod (shadow_addr y) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr y) 8 ltac:(lia)).
  unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *. lia. }
split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
{ intros a Ha. destruct (Hb a Ha) as (Hwr & Hown & Hnw). split; [|split; [exact Hown | lia]].
  apply (writable_at_same (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') a); [|exact Hwr].
  apply Hfr. rewrite unsigned_lit_small by lia. exact Hnw. }
split; [exact Hamr|]. split.
{ eapply range_addressable_agree; [|exact Hra]. intros y Hy. change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
  destruct (SH y ltac:(lia)) as (S1 & S2 & S3).
  pose proof (Z.div_mod (shadow_addr y) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr y) 8 ltac:(lia)).
  apply AV; lia. }
{ intros s Hs. rewrite AV; [exact (Hhull s Hs) | |];
  destruct (SH (amf_buf MS) ltac:(lia)) as (S1 & S2 & S3);
  destruct (SH (amf_buf MS + amf_size MS - 1) ltac:(lia)) as (T1 & T2 & T3);
  pose proof (Z.div_mod (shadow_addr (amf_buf MS)) 8 ltac:(lia));
  pose proof (Z.mod_pos_bound (shadow_addr (amf_buf MS)) 8 ltac:(lia)); lia. }
Qed.

(* ==========================================================================
   4. musl rewind
   ========================================================================== *)

Hypothesis HFS : afseeko0_mf_realizes tfibsegs B link_amf LA_FSEEKO.

Theorem link_arewind_musl : arewind_mf_realizes tfibsegs B link_amf LA_REWIND.
Proof.
intros ly S W regs mem md f k fl om wend wpos wbase pos len pb HPRE Hstk Hpres G10 Hblk Hk Hdyn Hpend Hlen Hbuf Hgot Hguard.
pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_stk_ceil ly HLY) as Lceil.
pose proof (amf_block_facts tfibsegs B LAWS ly S W mem md f HAR Hblk) as (F16 & F4k & Fceil & Fapp & Fby & _ & _).
pose proof (ts_errno B TB) as HERR.
assert (KS : ARW_STK = 4256 /\ AFS_STK = 4224 /\ ESTACK = 4096 /\ AMF_BLOCK = 1304 /\ AMF_ZEROED = 272 /\
  TFIB_ERRNO = 0x631b6c /\ amf_buf link_amf = 0x62fee0 /\ amf_size link_amf = 4096 /\ AF_NORD = 4 /\ AF_ERR = 32 /\
  AMF_BUF = 280 /\ AMF_BUFSIZ = 1024)
  by (repeat split; reflexivity).
destruct KS as (KA & KF & KE & KB & KZ & KERR & KBUF & KSZ & KNORD & KERR2 & KBF & KBS).
unfold ASAN_CEIL in Lceil. unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
pose proof alloc_ceiling_lt as Hcl.
set (sp0 := spZ regs) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
assert (Hfs : f + AMF_BLOCK + ARW_STK <= sp0) by lia.
unfold cfg_at. change (w64 LA_REWIND) with (Z_to_bv 64 LA_REWIND).
set (E := Ereg regs []).
assert (EREG : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
  by (intros i r Hi; apply ew_Ereg_nat; exact Hi).
pose proof (EREG 1%nat 1%bv eq_refl) as ER1. pose proof (EREG 2%nat 2%bv eq_refl) as ER2.
pose proof (EREG 3%nat 3%bv eq_refl) as ER3. pose proof (EREG 4%nat 4%bv eq_refl) as ER4.
pose proof (EREG 10%nat 10%bv eq_refl) as ER10.
assert (U2 : bv_unsigned (ew E 2) = sp0) by (rewrite ER2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = f) by (rewrite ER10, G10; unfold w64; apply unsigned_lit_small; lia).
(* the entry state: the frame, and the lock word *)
assert (HS0 : st_ok tfibsegs E ssM (restrict (w_H W) (mkst regs (Z_to_bv 64 LA_REWIND) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssM. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (region_ok_stack tfibsegs E _ 2 sp0 (-32)); [exact U2 | lia | lia |].
      intros a Ha. apply apresent_writable. apply HpresE. lia.
    + unfold region_ok, R_lock. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U10.
      split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      constructor; [|constructor].
      eapply (chunk_ok_val tfibsegs _ _ f 140 4 (SLit 0xffffffff) 0xffffffff); [reflexivity | zside | zside |].
      pose proof Hk as [(_ & _ & _ & Hst & _) _]. unfold amemfile_static in Hst.
      destruct Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & _). exact Hl.
  - apply pairwise_disjoint_of_extents. unfold R_stkM, R_lock, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U10. change (2 ^ 4) with 16. repeat split; first [exact Hal16 | exact F16 | lia]. }
(* +0x00 .. +0x6c: the run to the call of __fseeko_unlocked *)
eapply SRr_bind; [exact (rw_run_to W E LA_FSEEKO ssM eM _ md HS0 r_M)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
cbn [ms_mem mkst] in HF1, HFr1.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS1 eq_refl) as Hshape1.
rewrite Hshape1.
rreg HS1 (1%bv : bv 5) R1. rreg HS1 (2%bv : bv 5) R2. rreg HS1 (3%bv : bv 5) R3. rreg HS1 (4%bv : bv 5) R4.
rreg HS1 (8%bv : bv 5) R8. rreg HS1 (10%bv : bv 5) R10. rreg HS1 (11%bv : bv 5) R11. rreg HS1 (12%bv : bv 5) R12.
assert (OUT1 : forall y : word, ~ (sp0 - 32 <= bv_unsigned y < sp0) -> ms_mem ms1 y = mem y).
{ intros y Hy. apply HF1. intros Hin. apply Hy.
  pose proof (in_wrange_single_b E (ss_mem ssM) _ 2 (-32) 0 sp0 ltac:(vm_compute; reflexivity) U2 Hin). lia. }
assert (OUT1r : forall y : word, ~ (sp0 - 32 <= bv_unsigned y < sp0) ->
  mrestrict (w_H W) (ms_mem ms1) y = mrestrict (w_H W) mem y).
{ intros y Hy. apply HFr1. intros Hin. apply Hy.
  pose proof (in_wrange_single_b E (ss_mem ssM) _ 2 (-32) 0 sp0 ltac:(vm_compute; reflexivity) U2 Hin). lia. }
clear HF1 HFr1.
assert (PRS1 : forall a, sp0 - 32 <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent (w_H W) E eM ms1 0 _ a HS1 eq_refl);
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite U2; lia
  | unfold TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia]. }
assert (PM1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
  by exact (pres_move (w_H W) mem _ _ _ OUT1 PRS1).
assert (MB1 : forall x, f <= x < f + AMF_BLOCK ->
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms1)) x = mbyte tfibsegs (mrestrict (w_H W) mem) x).
{ intros x Hx. unfold mbyte. rewrite OUT1r; [reflexivity|]. rewrite unsigned_lit_small by lia. lia. }
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) ->
  aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. apply aview_eq_of. apply OUT1r. rewrite unsigned_lit_small by lia. exact Hn. }
(* the saved ra, s0, s1 *)
assert (SV1 : forall (j : nat) off (rz : bv 5) (n : nat),
  nth_error (YP09.r_chunks (hd R_stkM (ss_mem eM))) j = Some (YP09.mkChunk off (CVal 8 (SOff n 0))) ->
  ew E n = getr regs rz ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs rz))).
{ intros j off rz n Hj Hn. rewrite <- U2.
  refine (chunk_val_nth (w_H W) E eM ms1 0 j _ off 8 (SOff n 0) _ HS1 eq_refl Hj _ _ _).
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (u64_range (getr regs rz)). zside.
  - zside. }
pose proof (SV1 2%nat (-8) 1%bv 1%nat eq_refl ER1) as SRA.
pose proof (SV1 1%nat (-16) 8%bv 8%nat eq_refl (EREG 8%nat 8%bv eq_refl)) as SS0.
pose proof (SV1 0%nat (-24) 9%bv 9%nat eq_refl (EREG 9%nat 9%bv eq_refl)) as SS1.
clear SV1.
set (regs1 := ms_regs ms1) in *. set (mem1 := ms_mem ms1) in *.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (Hsp1 : spZ regs1 = sp0 - 32) by (unfold spZ; rewrite R2, U2; apply unsigned_lit_small; lia).
assert (HAR1 : AR tfibsegs B ly S W mem1 md1).
{ apply (AR_win_move ly S W mem md mem1 md1 (sp0 - 32) sp0 HAR);
  [lia | lia | | exact OUT1 | exact PRS1 | | apply with_vm_backing_same].
  - intros a Ha. apply (al_stack _ _ LAWS ly S W mem md a HAR). lia.
  - intros a Ha. apply HpresE. lia. }
(* the premises of __fseeko_unlocked at sp - 32 *)
assert (P1 : ecall_pre tfibsegs B ly S W regs1 mem1 md1).
{ split; [exact HAR1|]. split; [rewrite R1; apply ret_ok_lit; [lia | reflexivity]|].
  split; [rewrite Hsp1; replace (sp0 - 32) with (sp0 + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
  split; [rewrite Hsp1; lia|]. split; [rewrite Hsp1; lia|].
  split; [intros a Ha; rewrite Hsp1 in Ha; apply PM1; apply Hpres; lia|].
  split; [rewrite R3, ER3; exact Hgp | rewrite R4, ER4; exact Htp]. }
assert (P2 : ly_stk_lo ly + AFS_STK <= spZ regs1) by (rewrite Hsp1; lia).
assert (P3 : forall a, spZ regs1 - AFS_STK <= a < spZ regs1 -> apresent (w_H W) mem1 a)
  by (intros a Ha; rewrite Hsp1 in Ha; apply PM1; apply Hpres; lia).
assert (P4 : getr regs1 10 = w64 f) by (rewrite R10, ER10; exact G10).
assert (P5 : getr regs1 11 = w64 0) by (rewrite R11; reflexivity).
assert (P6 : getr regs1 12 = w64 0) by (rewrite R12; reflexivity).
destruct (amf_move tfibsegs link_amf _ _ f k fl om wend wpos wbase pos len pb MB1 Hk Hdyn Hpend Hlen) as (P8 & P9 & P10).
assert (P12 : amf_buf_ok tfibsegs B link_amf AFS_STK ly S W regs1 mem1).
{ apply (amf_buf_ok_move link_amf ARW_STK AFS_STK ly S W regs regs1 mem mem1 Hbuf);
  [rewrite Hsp1; lia | rewrite Hsp1; lia | unfold kHighMemBeg; lia |].
  intros x Hx. apply OUT1r. lia. }
assert (RW : forall a, 0 <= a -> a + 8 <= 0x700000 -> forall i, 0 <= i < 8 ->
  aview tfibsegs (w_H W) mem1 (a + i) = aview tfibsegs (w_H W) mem (a + i))
  by (intros a Ha0 Ha i Hi; apply AV1; lia).
assert (P13 : rdword (aview tfibsegs (w_H W) mem1) LA_GOT_GUARD = Some LA_GUARD)
  by (rewrite (rdword_ext (aview tfibsegs (w_H W) mem)) by (apply RW; unfold LA_GOT_GUARD; lia); exact Hgot).
assert (P14 : exists g, rdword (aview tfibsegs (w_H W) mem1) LA_GUARD = Some g).
{ destruct Hguard as (g & Hg). exists g.
  rewrite (rdword_ext (aview tfibsegs (w_H W) mem)) by (apply RW; unfold LA_GUARD; lia). exact Hg. }
(* +0x6c: __fseeko_unlocked(f, 0, SEEK_SET) *)
eapply SRr_bind; [exact (HFS ly S W regs1 mem1 md1 f k fl om wend wpos wbase pos len pb
  P1 P2 P3 P4 P5 P6 Hblk P8 P9 P10 Hlen P12 P13 P14)|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hpost). cbv zeta in Hpost.
destruct Hpost as (-> & HAR2 & HP2 & Hsbm2 & Hk2 & Hpend2 & Hz2 & Harm1 & Harm2 & Hkept2 & Hpm2 & Hpw2).
rewrite Hsp1 in Hkept2, Hpw2.
assert (RA1 : raZ regs1 = RA_FS) by (unfold raZ, RA_FS; rewrite R1; apply unsigned_lit_small; lia).
rewrite RA1.
(* the frame and the saved registers across the call *)
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 - AFS_STK <= a < sp0 - 32) -> ~ (f <= a < f + AMF_ZEROED) ->
  ~ (0x62fee0 <= a < 0x62fee0 + 4096) -> ~ (0x631b6c <= a < 0x631b6c + 4) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem1 a).
{ intros a Ha H1 H2 H3 H4. apply Hkept2; [exact Ha | exact H1 | exact H2 | rewrite KBUF, KSZ; exact H3 |].
  rewrite HERR, KERR. exact H4. }
assert (SVK : forall off v, -24 <= off <= -8 -> val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 + off) 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 + off) 8 v).
{ intros off v Ho Hv. apply (val_mem_kept (w_H W) (w_H W) mem1 mem2); [|exact Hv].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply AV2; lia. }
pose proof (SVK (-8) _ ltac:(lia) SRA) as SRA2. pose proof (SVK (-16) _ ltac:(lia) SS0) as SS02.
pose proof (SVK (-24) _ ltac:(lia) SS1) as SS12. clear SVK SRA SS0 SS1.
assert (G8_2 : getr regs2 8 = w64 f)
  by (rewrite (ap_lit regs1 regs2 8%bv 8 HP2 ltac:(unfold acallee_saved; lia) eq_refl), R8, ER10; exact G10).
assert (G2_2 : getr regs2 2 = Z_to_bv 64 (sp0 - 32))
  by (rewrite (ap_lit regs1 regs2 2%bv 2 HP2 ltac:(unfold acallee_saved; lia) eq_refl), R2, U2; reflexivity).
assert (FBY2 : forall a, f <= a < f + AMF_BLOCK ->
  apresent (w_H W) mem2 a /\ ~ aowned B ly S a /\ ~ in_img tfibsegs a).
{ intros a Ha. destruct (Fby a Ha) as (Hp & Ho & Hi). split; [|split; [exact Ho | exact Hi]].
  apply Hpm2. apply PM1. exact Hp. }
(* the flags word after the call: F_NORD, or F_NORD | F_ERR *)
assert (FL : exists fl', (fl' = 4 \/ fl' = 36) /\ val_mem tfibsegs (mrestrict (w_H W) mem2) f 4 fl').
{ pose proof Hk2 as [(_ & _ & _ & _ & [Hf | Hf] & _) _]; rewrite Z.add_0_r in Hf;
  [exists 4 | exists 36]; (split; [lia | exact Hf]). }
destruct FL as (fl' & Hfl' & Hv2).
(* +0x70 .. +0x8c *)
set (Ep := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9]).
assert (Ep_2 : bv_unsigned (ew Ep 2) = sp0 - 32)
  by (unfold Ep; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), G2_2; apply unsigned_lit_small; lia).
assert (Ep_8 : bv_unsigned (ew Ep 8) = f)
  by (unfold Ep; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), G8_2; apply unsigned_lit_small; lia).
assert (Ep_32 : ew Ep 32 = getr regs 1) by (unfold Ep; exact (ew_Ereg_extra regs2 _ 0)).
assert (Ep_33 : ew Ep 33 = getr regs 8) by (unfold Ep; exact (ew_Ereg_extra regs2 _ 1)).
assert (Ep_34 : ew Ep 34 = getr regs 9) by (unfold Ep; exact (ew_Ereg_extra regs2 _ 2)).
assert (HSE : st_ok tfibsegs Ep (ssE fl') (restrict (w_H W) (mkst regs2 (Z_to_bv 64 RA_FS) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssE.
  apply (entry_st_ok_full tfibsegs); change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9]) with Ep.
  - apply regs_ok_Ereg.
  - destruct Hfl' as [-> | ->]; vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, R_stkE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Ep_2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * eapply (chunk_ok_val tfibsegs _ _ (sp0 - 32) 24 8 _ (bv_unsigned (getr regs 1)));
        [cbn [sv_denot]; rewrite Ep_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (u64_range (getr regs 1)); zside | zside |].
        replace (sp0 - 32 + 24) with (sp0 + -8) by lia. exact SRA2.
      * eapply (chunk_ok_val tfibsegs _ _ (sp0 - 32) 16 8 _ (bv_unsigned (getr regs 8)));
        [cbn [sv_denot]; rewrite Ep_33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (u64_range (getr regs 8)); zside | zside |].
        replace (sp0 - 32 + 16) with (sp0 + -16) by lia. exact SS02.
      * eapply (chunk_ok_val tfibsegs _ _ (sp0 - 32) 8 8 _ (bv_unsigned (getr regs 9)));
        [cbn [sv_denot]; rewrite Ep_34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (u64_range (getr regs 9)); zside | zside |].
        replace (sp0 - 32 + 8) with (sp0 + -24) by lia. exact SS12.
    + unfold region_ok, R_flE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Ep_8.
      split; [lia|]. split; [lia|].
      split; [intros o Ho; apply apresent_writable; exact (proj1 (FBY2 (f + o) ltac:(lia)))|].
      constructor; [|constructor].
      eapply (chunk_ok_val tfibsegs _ _ f 0 4 (SLit fl') fl'); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Hv2.
  - apply pairwise_disjoint_of_extents. unfold R_stkE, R_flE, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Ep_2, Ep_8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Ep_2. change (2 ^ 4) with 16.
    repeat split; first [lia | (replace (sp0 - 32) with (sp0 + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16)]. }
assert (r_E : RUN (ssE fl') = (eE, RS_stopped (SR_jalr (SOff 32 0))))
  by (destruct Hfl' as [-> | ->]; [exact r_E4 | exact r_E36]).
change (cfg_at tfibsegs RA_FS regs2 mem2 md2) with (mkCfg (mkst regs2 (Z_to_bv 64 RA_FS) mem2 (seg_rom tfibsegs)) md2).
eapply SRr_bind; [exact (rw_run W Ep (ssE fl') eE _ _ md2 HSE r_E)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3).
cbn [ms_mem mkst] in HF3, HFr3.
assert (WIN3 : forall a, in_wrange Ep (ss_mem (ssE fl')) a -> f + 0 <= a < f + 4).
{ intros a Ha. exact (in_wrange_single_b Ep (ss_mem (ssE fl')) _ 8 0 4 f
    ltac:(destruct Hfl' as [-> | ->]; vm_compute; reflexivity) Ep_8 Ha). }
assert (OUT3 : forall y : word, ~ (f <= bv_unsigned y < f + 4) -> ms_mem ms3 y = mem2 y).
{ intros y Hy. apply HF3. intros Hin. apply Hy. pose proof (WIN3 _ Hin). lia. }
assert (OUT3r : forall y : word, ~ (f <= bv_unsigned y < f + 4) ->
  mrestrict (w_H W) (ms_mem ms3) y = mrestrict (w_H W) mem2 y).
{ intros y Hy. apply HFr3. intros Hin. apply Hy. pose proof (WIN3 _ Hin). lia. }
clear HF3 HFr3 WIN3.
assert (PRS3 : forall a, f <= a < f + 4 -> apresent (w_H W) (ms_mem ms3) a).
{ intros a Ha. apply apresent_of_writable; [lia | exact (proj2 (proj2 (FBY2 a ltac:(lia)))) |].
  apply (window_writable (w_H W) Ep eE ms3 1 _ a HS3 eq_refl).
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite Ep_8. lia. }
assert (FL3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms3)) f 4 AF_NORD).
{ pose proof (chunk_val_nth (w_H W) Ep eE ms3 1 0 _ 0 4 (SLit 4) 4 HS3 eq_refl eq_refl eq_refl
    ltac:(zside) ltac:(zside)) as X.
  cbn [YP09.r_base base_val] in X. rewrite Ep_8, Z.add_0_r in X. exact X. }
assert (MB3 : forall x, f + 4 <= x < f + AMF_BLOCK \/ (0 <= x < 2 ^ 64 /\ ~ (f <= x < f + 4)) ->
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms3)) x = mbyte tfibsegs (mrestrict (w_H W) mem2) x).
{ intros x Hx. unfold mbyte. rewrite OUT3r; [reflexivity|]. rewrite unsigned_lit_small by lia. lia. }
assert (AV3 : forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + 4) ->
  aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) mem2 a).
{ intros a Ha Hn. apply aview_eq_of. apply OUT3r. rewrite unsigned_lit_small by lia. exact Hn. }
rreg HS3 (1%bv : bv 5) Q1. rreg HS3 (Z_to_bv 5 2) Q2. rreg HS3 (Z_to_bv 5 8) Q8. rreg HS3 (Z_to_bv 5 9) Q9.
eapply (SRr_ret_at tfibsegs rw_tbl rw_tbl_ok Hwx W Ep); [exact HS3 | reflexivity | vm_compute; reflexivity |].
intros mat'.
replace (v_jalr (getr (ms_regs ms3) 1) 0) with (w64 (raZ regs))
  by (rewrite Q1, Ep_32; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
assert (SBM23 : same_but_materialized md2
  (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat3 md2)) mat' (with_vm_backing (m_vm_lazy md2) mat3 md2)))
  by exact (same_but_materialized_trans _ _ _ (with_vm_backing_same md2 mat3) (with_vm_backing_same _ mat')).
cbv beta. split; [reflexivity|]. do 3 eexists. split; [reflexivity|].
(* the post *)
assert (Hn1 : amf_n1 link_amf k pos <= k) by (unfold amf_n1; lia).
assert (Hlt : amf_n1 link_amf k pos < k \/ amf_n1 link_amf k pos = k) by lia.
assert (DK : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms3)) f 0 /\
  amf_dyn tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms3)) f AF_NORD om 0 0 0
  (if amf_n1 link_amf k pos <? k then pos + amf_n1 link_amf k pos else 0) (Z.max len (pos + amf_n1 link_amf k pos))).
{ destruct Hlt as [Hlt | Heq].
  - rewrite (proj2 (Z.ltb_lt _ _) Hlt). destruct (Harm1 Hlt) as (_ & Hd).
    exact (amf_flags_set tfibsegs link_amf _ _ f 0 _ om 0 0 0 _ _ (fun x Hx => MB3 x (or_introl Hx)) FL3 Hk2 Hd).
  - rewrite (proj2 (Z.ltb_ge (amf_n1 link_amf k pos) k) ltac:(lia)). destruct (Harm2 Heq) as (_ & Hd). rewrite Heq.
    exact (amf_flags_set tfibsegs link_amf _ _ f 0 _ om 0 0 0 _ _ (fun x Hx => MB3 x (or_introl Hx)) FL3 Hk2 Hd). }
destruct DK as (K3 & DYN).
assert (Hpk : k <= AMF_BUFSIZ) by (destruct Hk as [_ [(-> & _) | (Hb & _)]]; lia).
assert (PM3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms3) a).
{ intros a Hp. apply (pres_move (w_H W) mem2 (ms_mem ms3) f (f + 4) OUT3 PRS3). apply Hpm2. apply PM1. exact Hp. }
split; [|split; [|split; [|split; [exact K3 | split; [|split; [|split; [exact DYN | split; [|split]]]]]]]].
- (* AR *)
  apply (AR_win_move ly S W mem2 md2 (ms_mem ms3) _ f (f + 4) HAR2); [lia | lia | | exact OUT3 | exact PRS3 | | exact SBM23].
  + intros a Ha. exact (proj1 (proj2 (FBY2 a ltac:(lia)))).
  + intros a Ha. exact (proj1 (FBY2 a ltac:(lia))).
- (* the callee-saved registers *)
  intros r Hr.
  destruct (Z.eq_dec r 2) as [-> | N2].
  { rewrite Q2, Ep_2. replace (sp0 - 32 + 32) with sp0 by lia. unfold sp0, spZ. rewrite Z_to_bv_bv_unsigned.
    f_equal; apply bv_eq; reflexivity. }
  destruct (Z.eq_dec r 8) as [-> | N8].
  { rewrite Q8, Ep_33. f_equal; apply bv_eq; reflexivity. }
  destruct (Z.eq_dec r 9) as [-> | N9].
  { rewrite Q9, Ep_34. f_equal; apply bv_eq; reflexivity. }
  pose proof (acs_kept r Hr N2 N8 N9) as HK.
  rewrite (kept_regs (w_H W) Ep eE ms3 regs2 _ HS3 eq_refl kept_eE r HK).
  rewrite (HP2 r Hr).
  exact (kept_regs (w_H W) E eM ms1 regs [] HS1 eq_refl kept_eM r HK).
- (* the model *)
  exact (same_but_materialized_trans _ _ _ (with_vm_backing_same md mat1) (same_but_materialized_trans _ _ _ Hsbm2 SBM23)).
- (* the pending bytes *)
  apply (azbytes_move tfibsegs (mrestrict (w_H W) mem2)); [|exact Hpend2].
  intros i Hi. apply MB3. left. lia.
- (* g_said *)
  apply (azbytes_move tfibsegs (mrestrict (w_H W) mem2)); [|exact Hz2].
  intros i Hi. rewrite length_firstn in Hi. apply MB3. right.
  assert (Hpl : 0 <= pos <= len /\ len <= amf_size link_amf) by (destruct Hdyn as (_ & _ & _ & _ & _ & Hp & Hl & _); lia).
  assert (Hhi : pos + amf_n1 link_amf k pos <= amf_size link_amf) by (unfold amf_n1; lia).
  assert (Hin : 0x62fee0 <= amf_buf link_amf + pos + Z.of_nat i < 0x62fee0 + 4096).
  { assert (Z.of_nat i < amf_n1 link_amf k pos) by lia. lia. }
  split; [lia|]. intros Hf. apply (proj2 (proj2 (FBY2 (amf_buf link_amf + pos + Z.of_nat i) ltac:(lia)))).
  exact (said_img _ Hin).
- (* every byte outside the window, the FILE's first 272 bytes, g_said and errno *)
  intros a Ha Hw Hf Hb He. rewrite AV3 by lia.
  rewrite AV2; [| exact Ha | lia | exact Hf | rewrite <- KBUF, <- KSZ; exact Hb | rewrite HERR, KERR in He; exact He].
  apply AV1; [exact Ha | lia].
- exact PM3.
- intros a Ha. apply PM3. apply Hpres. exact Ha.
Qed.

(* ==========================================================================
   5. ___interceptor_rewind and its trampoline
   ========================================================================== *)

Lemma icpt_walk : forall pc, RUNTO LA_REWIND (ssI pc) = (eI, RS_running) -> arewind_mf_realizes tfibsegs B link_amf pc.
Proof.
intros pc Hrun ly S W regs mem md f k fl om wend wpos wbase pos len pb HPRE Hstk Hpres G10 Hblk Hk Hdyn Hpend Hlen Hbuf Hgot Hguard.
pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_stk_ceil ly HLY) as Lceil.
pose proof (amf_block_facts tfibsegs B LAWS ly S W mem md f HAR Hblk) as (F16 & F4k & Fceil & Fapp & Fby & _ & _).
assert (KS : ARW_STK = 4256 /\ ESTACK = 4096 /\ AMF_BLOCK = 1304) by (repeat split; reflexivity).
destruct KS as (KA & KE & KB).
unfold ASAN_CEIL in Lceil. unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
pose proof alloc_ceiling_lt as Hcl.
set (sp0 := spZ regs) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
assert (Hfs : f + AMF_BLOCK + ARW_STK <= sp0) by lia.
unfold cfg_at at 1. change (w64 pc) with (Z_to_bv 64 pc).
set (E := Ereg regs []).
assert (EREG : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
  by (intros i r Hi; apply ew_Ereg_nat; exact Hi).
pose proof (EREG 2%nat 2%bv eq_refl) as ER2.
assert (U2 : bv_unsigned (ew E 2) = sp0) by (rewrite ER2; reflexivity).
(* the entry state: the two frames, and AR's two constant rows *)
assert (HS0 : st_ok tfibsegs E (ssI pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssI. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|exact (rodata_ok B TB rw_rodata ly S (w_H W) mem E (rw_rodata_chk ly) (proj1 HAR))].
    apply (region_ok_stack tfibsegs E _ 2 sp0 (-32)); [exact U2 | lia | lia |].
    intros a Ha. apply apresent_writable. apply HpresE. lia.
  - apply pairwise_disjoint_of_extents. unfold R_stkI, rw_rodata, ro_region, extent_of_region.
    cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite U2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2. change (2 ^ 4) with 16. repeat split; first [exact Hal16 | lia]. }
(* the wrapper, TryAsanInitFromRtl's early return, and jr t1 *)
eapply SRr_bind; [exact (rw_run_to W E LA_REWIND (ssI pc) eI _ md HS0 Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
cbn [ms_mem mkst] in HF1, HFr1.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS1 eq_refl) as Hshape1.
rewrite Hshape1.
rreg HS1 (1%bv : bv 5) R1. rreg HS1 (2%bv : bv 5) R2. rreg HS1 (3%bv : bv 5) R3. rreg HS1 (4%bv : bv 5) R4.
rreg HS1 (10%bv : bv 5) R10.
assert (WB : forallb (fun t => win_eqb t (Some 2%nat, -32, 0) || (snd t <=? snd (fst t))) (windows (ss_mem (ssI pc))) = true)
  by (vm_compute; reflexivity).
assert (OUT1 : forall y : word, ~ (sp0 - 32 <= bv_unsigned y < sp0) -> ms_mem ms1 y = mem y).
{ intros y Hy. apply HF1. intros Hin. apply Hy. pose proof (in_wrange_single_b E _ _ 2 (-32) 0 sp0 WB U2 Hin). lia. }
assert (OUT1r : forall y : word, ~ (sp0 - 32 <= bv_unsigned y < sp0) ->
  mrestrict (w_H W) (ms_mem ms1) y = mrestrict (w_H W) mem y).
{ intros y Hy. apply HFr1. intros Hin. apply Hy. pose proof (in_wrange_single_b E _ _ 2 (-32) 0 sp0 WB U2 Hin). lia. }
clear HF1 HFr1.
assert (PRS1 : forall a, sp0 - 32 <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent (w_H W) E eI ms1 0 _ a HS1 eq_refl);
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite U2; lia
  | unfold TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia]. }
assert (PM1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
  by exact (pres_move (w_H W) mem _ _ _ OUT1 PRS1).
assert (MB1 : forall x, f <= x < f + AMF_BLOCK ->
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms1)) x = mbyte tfibsegs (mrestrict (w_H W) mem) x).
{ intros x Hx. unfold mbyte. rewrite OUT1r; [reflexivity|]. rewrite unsigned_lit_small by lia. lia. }
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) ->
  aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hn. apply aview_eq_of. apply OUT1r. rewrite unsigned_lit_small by lia. exact Hn. }
assert (AP1 : aregs_preserved regs (ms_regs ms1))
  by exact (aregs_preserved_of_st_ok (w_H W) E eI ms1 regs [] HS1
    ltac:(split; [intros i Hi; reflexivity | reflexivity]) ltac:(vm_compute; reflexivity)).
set (regs1 := ms_regs ms1) in *. set (mem1 := ms_mem ms1) in *.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (Hsp1 : spZ regs1 = sp0) by (unfold spZ; rewrite R2, ER2; reflexivity).
assert (Q1 : getr regs1 1 = getr regs 1) by (rewrite R1; exact (EREG 1%nat 1%bv eq_refl)).
assert (HAR1 : AR tfibsegs B ly S W mem1 md1).
{ apply (AR_win_move ly S W mem md mem1 md1 (sp0 - 32) sp0 HAR);
  [lia | lia | | exact OUT1 | exact PRS1 | | apply with_vm_backing_same].
  - intros a Ha. apply (al_stack _ _ LAWS ly S W mem md a HAR). lia.
  - intros a Ha. apply HpresE. lia. }
(* musl rewind's premises at the same sp and ra *)
assert (P1 : ecall_pre tfibsegs B ly S W regs1 mem1 md1).
{ split; [exact HAR1|]. split; [rewrite Q1; exact Hra|].
  split; [rewrite Hsp1; exact Hal16|]. split; [rewrite Hsp1; lia|]. split; [rewrite Hsp1; lia|].
  split; [intros a Ha; rewrite Hsp1 in Ha; apply PM1; apply HpresE; exact Ha|].
  split; [rewrite R3, (EREG 3%nat 3%bv eq_refl); exact Hgp | rewrite R4, (EREG 4%nat 4%bv eq_refl); exact Htp]. }
assert (P2 : ly_stk_lo ly + ARW_STK <= spZ regs1) by (rewrite Hsp1; exact Hstk).
assert (P3 : forall a, spZ regs1 - ARW_STK <= a < spZ regs1 -> apresent (w_H W) mem1 a)
  by (intros a Ha; rewrite Hsp1 in Ha; apply PM1; apply Hpres; exact Ha).
assert (P4 : getr regs1 10 = w64 f) by (rewrite R10, (EREG 10%nat 10%bv eq_refl); exact G10).
destruct (amf_move tfibsegs link_amf _ _ f k fl om wend wpos wbase pos len pb MB1 Hk Hdyn Hpend Hlen) as (P8 & P9 & P10).
assert (P12 : amf_buf_ok tfibsegs B link_amf ARW_STK ly S W regs1 mem1).
{ apply (amf_buf_ok_move link_amf ARW_STK ARW_STK ly S W regs regs1 mem mem1 Hbuf);
  [rewrite Hsp1; lia | rewrite Hsp1; lia | unfold kHighMemBeg; lia |].
  intros x Hx. apply OUT1r. lia. }
assert (RW : forall a, 0 <= a -> a + 8 <= 0x700000 -> forall i, 0 <= i < 8 ->
  aview tfibsegs (w_H W) mem1 (a + i) = aview tfibsegs (w_H W) mem (a + i))
  by (intros a Ha0 Ha i Hi; apply AV1; lia).
assert (P13 : rdword (aview tfibsegs (w_H W) mem1) LA_GOT_GUARD = Some LA_GUARD)
  by (rewrite (rdword_ext (aview tfibsegs (w_H W) mem)) by (apply RW; unfold LA_GOT_GUARD; lia); exact Hgot).
assert (P14 : exists g, rdword (aview tfibsegs (w_H W) mem1) LA_GUARD = Some g).
{ destruct Hguard as (g & Hg). exists g.
  rewrite (rdword_ext (aview tfibsegs (w_H W) mem)) by (apply RW; unfold LA_GUARD; lia). exact Hg. }
eapply SRr_mono; [exact (link_arewind_musl ly S W regs1 mem1 md1 f k fl om wend wpos wbase pos len pb
  P1 P2 P3 P4 Hblk P8 P9 P10 Hlen P12 P13 P14)|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsbm2 & Hk2 & Hpend2 & Hz2 & Hdyn2 & Hkept2 & Hpm2 & Hpw2).
rewrite Hsp1 in Hkept2, Hpw2.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold raZ; rewrite Q1; reflexivity|].
split; [exact HAR2|]. split; [exact (aregs_preserved_trans _ _ _ AP1 HP2)|].
split; [exact (same_but_materialized_trans _ _ _ (with_vm_backing_same md mat1) Hsbm2)|].
split; [exact Hk2|]. split; [exact Hpend2|]. split; [exact Hz2|]. split; [exact Hdyn2|].
split; [|split].
- intros a Ha Hw Hf Hb He. rewrite (Hkept2 a Ha Hw Hf Hb He). apply AV1; [exact Ha | lia].
- intros a Hp. apply Hpm2. apply PM1. exact Hp.
- exact Hpw2.
Qed.

Theorem link_arewind_icpt : arewind_mf_realizes tfibsegs B link_amf LA_I_REWIND.
Proof. exact (icpt_walk LA_I_REWIND r_II). Qed.

Theorem link_arewind_mf_ok : arewind_mf_realizes tfibsegs B link_amf LA_W_REWIND.
Proof. exact (icpt_walk LA_W_REWIND r_IW). Qed.

End S.
End d.

Print Assumptions link_arewind_musl.
Print Assumptions link_arewind_icpt.
Print Assumptions link_arewind_mf_ok.
About link_arewind_musl.
About link_arewind_icpt.
About link_arewind_mf_ok.
