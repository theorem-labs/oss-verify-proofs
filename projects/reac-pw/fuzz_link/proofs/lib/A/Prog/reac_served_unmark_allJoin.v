(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v; 366 of its 417 lines of code are new or changed and 540 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4, listing offset AF_reac_served_unmark_all) on image A, THE JOIN
   PIECE (the loop latch): from JOIN (+0x294, round c, name c done) to HEAD (+0x1d8, round c + 1) or TAIL (+0x340).
     +0x294..+0x310  `sb s8, k(s2)` for k = 4 .. 0x23: the alias buffer's 32 shadow bytes := 0xf8 again
     +0x314  `lb a0, 0(s10)`: m's shadow byte, 0 (m's block is addressable, LinkWalkShadow.v shadow_transport of the
             call's range_addressable; its granule's last byte forces 0)
     +0x318  `bnez a0` not taken (the slow path +0x330 / errpath_load4 is not reached)
     +0x31c  `lw a0, 0(s4)` = m->n (the marks block's bytes, kept since the call)
     +0x320  s11 += 1; +0x324 s6 += 16
     +0x328  `blt s11, a0` -> HEAD with c + 1 < n; else +0x32c `j` +0x340, the TAIL with c + 1 = n.
   One plain run (the token engine refuses a writable shadow window) with three regions: F's shadow (writable at
   4 .. 0x24), m's shadow byte (a zero chunk) and m->n (the marks block's bytes as the environment's data 0), then
   the branch.
   It proves `um_join : um_tail_obl SK B -> forall c, um_head_obl SK B (S c) -> um_join_obl SK B c`.

   Proves no function (kind: segment lemma of reac_served_unmark_all's walk, the loop-latch piece). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YFen.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalk LinkWalkSide LinkWalkPi LinkWalkCall LinkWalkShadow LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_unmark_allDefs reac_served_unmark_allReadK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below is the Section's SK. *)
Fail Definition sink_head_probe_um_join : YI16.sink_head := _.

(* ==========================================================================
   0. The symbolic state at JOIN: atoms 0..31 are the registers at the cut; three regions
   ========================================================================== *)
Definition jn_SHR : YP09.region := YP09.mkRegion (Some 18%nat) 0 64 4 36 [].
Definition jn_MSH : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CZero 1)].
Definition jn_MN : YP09.region := YP09.mkRegion (Some 20%nat) 0 4 0 0 [YP09.mkChunk 0 (CData 0 0 4)].
Definition jn_facts : facts := mkFacts [(18%nat, mkAF 0x7fff8000 (0x7fff8000 + 2 ^ 44) 3)] [] [].
Definition jn_ss0 : sstate := mkSS UM_CUT_JOIN sr_atoms [jn_SHR; jn_MSH; jn_MN] None jn_facts.

(* a run that stops at a branch (urd_run_call for paj_run_plain_x) *)
Ltac urj_run RUN HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUN with
    | forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
        eapply (RUN W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
        [ clear Hrun | clear Hrun ]
      end
    end
  end.

(* the callee-saved registers but s6 and s11 keep their entry atoms *)
Ltac urj_cs_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in let H22 := fresh "H22" in let H27 := fresh "H27" in
  intros r Hr H22 H27; unfold acallee_saved in Hr;
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
     r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  clear Hr;
  repeat (destruct Hr' as [Hr0 | Hr']; [subst r; first [exfalso; lia | vm_compute; reflexivity]|]);
  subst r; first [exfalso; lia | vm_compute; reflexivity].

(* the write window of the three regions, at any state of the run *)
Ltac urj_wr Hr Hra U18 :=
  vm_compute in Hr; destruct Hr as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra; [rewrite U18 in Hra | lia | lia].

Local Set Default Proof Using "All".
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).

(* the environment: the registers, and the marks block's bytes as data 0 *)
Definition jn_env (regs : bvmap 5 word) (gbs : list byte) : env := Eimg (mkEnv (ew (Ereg regs [])) (fun _ => gbs)).

Lemma jn_ew : forall regs gbs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (jn_env regs gbs) n = getr regs r.
Proof.
  intros regs gbs n r Hr. unfold jn_env. rewrite Eimg_low; [exact (ew_Ereg_nat regs [] n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. lia.
Qed.

Lemma jn_ed : forall regs gbs, ed (jn_env regs gbs) 0 = gbs.
Proof. reflexivity. Qed.

Lemma jn_regs_ok : forall regs gbs, regs_ok (jn_env regs gbs) sr_atoms regs.
Proof.
  intros regs gbs. apply (regs_ok_agree_on (fun n => (n <? 32)%nat) (Ereg regs [])).
  - intros n Hn. apply Nat.ltb_lt in Hn. unfold jn_env. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
  - vm_compute. reflexivity.
  - apply regs_ok_Ereg.
Qed.

(* a register of a state of the run is its entry register plus the offset its atom carries *)
Lemma jn_reg : forall (H : word -> bool) regs gbs ss ms (r : Z) k,
  st_ok_pi SEGS VAL (jn_env regs gbs) ss (restrict H ms) -> 0 <= r < 32 ->
  sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) k ->
  getr (ms_regs ms) (Z_to_bv 5 r) = Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 r)) + k).
Proof.
  intros H regs gbs ss ms r k HS Hr Hsr. rewrite (st_ok_pi_restrict_reg H _ ss ms _ HS), Hsr. cbn [sv_denot].
  rewrite (jn_ew regs gbs (Z.to_nat r) (Z_to_bv 5 r))
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; rewrite Z.mod_small by lia; lia).
  reflexivity.
Qed.

Lemma jn_cs : forall (H : word -> bool) regs gbs ss ms,
  st_ok_pi SEGS VAL (jn_env regs gbs) ss (restrict H ms) ->
  (forall r, acallee_saved r -> r <> 22 -> r <> 27 -> sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0) ->
  forall r, acallee_saved r -> r <> 22 -> r <> 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
  intros H regs gbs ss ms HS Hsr r Hr H22 H27.
  assert (Hr5 : 0 <= r < 32) by (unfold acallee_saved in Hr; lia).
  rewrite (jn_reg H regs gbs ss ms r 0 HS Hr5 (Hsr r Hr H22 H27)), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* `blt s11, a0` with s11 = c + 1 and a0 the sign-extended m->n *)
Lemma jn_blt : forall E (c n : Z), bv_unsigned (ew E 27) = c -> data_word E 0 0 4 = n -> 0 <= c < 2 ^ 32 ->
  0 <= n <= 32 ->
  branch_taken BC_LT (sv_denot E (SOff 27 1)) (sv_denot E (SExt true 32 (SData 0 0 4))) = (c + 1 <? n).
Proof.
  intros E c n H27 Hn Hc Hn0.
  transitivity (Sg E (SOff 27 1) <? Sg E (SExt true 32 (SData 0 0 4))); [reflexivity|].
  assert (U1 : U E (SData 0 0 4) = n).
  { unfold U. cbn [sv_denot]. rewrite Hn. apply unsigned_lit_small. lia. }
  rewrite S_SOff, H27, (S_of_U E (SExt true 32 (SData 0 0 4))), U_SExt, U1.
  cbv iota. change (Z.of_N 32) with 32. rewrite (Z.mod_small n) by lia.
  rewrite swrap32_id by lia. rewrite zcanon_id by (unfold M64; lia).
  rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
(* the two read-only chunks: m's shadow byte (zero) and m->n (the environment's data 0) *)
Lemma jn_chunk_zero : forall E m base, mbyte SEGS m base = Some (Z_to_bv 8 0) ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk 0 (CZero 1)).
Proof.
  intros E m base H i Hi. assert (Hi1 : 0 <= i < 1) by exact Hi. assert (i = 0) by lia. subst i.
  exists (Z_to_bv 8 0). split; [reflexivity|].
  rewrite <- H. f_equal. transitivity (base + 0 + 0); [reflexivity | lia].
Qed.

Lemma jn_chunk_data : forall E m base gbs, ed E 0 = gbs ->
  (forall i, 0 <= i < 4 -> exists b, nth_error gbs (Z.to_nat i) = Some b /\ mbyte SEGS m (base + i) = Some b) ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk 0 (CData 0 0 4)).
Proof.
  intros E m base gbs Hd H i Hi. assert (Hi1 : 0 <= i < 4) by exact Hi. destruct (H i Hi1) as (b & Eb & Mb).
  exists b. split.
  - transitivity (nth_error (ed E 0) (Z.to_nat (0 + i))); [reflexivity|]. rewrite Hd, Z.add_0_l. exact Eb.
  - rewrite <- Mb. f_equal. transitivity (base + 0 + i); [reflexivity | lia].
Qed.
End p.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* AR's laws; the start-up symbols; the segments; the relro window: as reac_served_unmark_allReadK.v. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.

Section c.
Variable cx : umcx.
Variable fpos : Z.
Hypothesis HPRE : um_pre SK B cx.
Hypothesis HNIN : ~ In (UM_CID, fpos) (frames (um_Sc cx)).
Hypothesis HS1W : exists S1 W1 mem1 md1, AR SEGS B (um_lyc cx) S1 W1 mem1 md1 /\
  frames S1 = (UM_CID, fpos) :: frames (um_Sc cx) /\ ablocks B (um_lyc cx) S1 = ablocks B (um_lyc cx) (um_Sc cx).
#[local] Notation F := (um_F cx fpos).
#[local] Notation SH := (um_SH cx fpos).
#[local] Notation AJ ly S W m md :=
  (ajournal_gx SEGS B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
     (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) ((UM_CID, fpos) :: um_own cx) ly S W m md (um_k cx)).

(* m's shadow byte is 0 at every state of the walk *)
Lemma jn_mk_sh0 : forall ly3 S3 W3 m3 md3, AJ ly3 S3 W3 m3 md3 -> rk_inv SK B cx fpos ly3 S3 W3 m3 md3 ->
  mbyte SEGS (rdW W3 m3) (SHADOW_OFF + um_mk cx / 8) = Some (zb 0).
Proof.
  intros ly3 S3 W3 m3 md3 HJ3 HI.
  pose proof HI as (_ & Hfrs & _ & Hperm & Hfa & _ & _ & _ & HK & _ & _ & _ & Hm & _).
  pose proof HPRE as ((HJ & HGX & _) & _).
  destruct (rk_mk SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W Hm) as (M0 & M1 & M2 & M3 & _).
  assert (HAR3 : AR SEGS B ly3 S3 W3 m3 md3) by (destruct HJ3 as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
  pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (L1 & H1).
  pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (L2 & H2).
  assert (HB : forall b mm, In (b, mm) (ablocks B (um_lyc cx) (um_Sc cx)) -> In (b, mm) (ablocks B ly3 S3))
    by (intros b mm Hb; exact (Permutation_in _ (Permutation_sym Hperm) Hb)).
  pose proof (rk_pre_ar SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as HAR0.
  pose proof (rk_fmiss SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as HFM.
  destruct (shadow_transport SEGS B LAWS TB pa_img_range (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx)
    ly3 S3 W3 m3 md3 (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx)
    (fun a => um_E cx a \/ aside_rng (um_lyc cx) UM_CID fpos a) (um_mk cx) MK_SIZE
    HAR0 HAR3 ltac:(congruence) ltac:(congruence) HB HK HFM ltac:(unfold MK_SIZE; lia)
    ltac:(intros x Hx; apply (sclass_of_ajw SK SEGS B LAWS (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx)
       (um_sp0 cx) (um_FP cx) (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx) (um_lyc cx)
       (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx) x HGX HJ
       (rk_mk_ajw SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W x Hm Hx));
       unfold amem_range, MK_SIZE in *; rk_consts; lia)
    M2 M3) as (RA1 & _).
  destruct (RA1 (8 * (um_mk cx / 8) + 7) ltac:(unfold MK_SIZE; lia)) as (s & Hs & Hok).
  unfold shadow_of_addr in Hs. replace ((8 * (um_mk cx / 8) + 7) / 8) with (um_mk cx / 8) in Hs by lia.
  destruct Hok as [-> | Hok]; [|exfalso; lia].
  unfold aview in Hs. destruct (mbyte SEGS (rdW W3 m3) (SHADOW_OFF + um_mk cx / 8)) as [b|] eqn:Eb; [|discriminate Hs].
  cbn [option_map] in Hs. injection Hs as Hb. f_equal. exact (rk_byte_zero b Hb).
Qed.

(* the registers of round c + 1 *)
Lemma jn_R_next : forall c (regs regs' : bvmap 5 word), urb_R cx fpos c regs ->
  (forall r, acallee_saved r -> r <> 22 -> r <> 27 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  getr regs' (Z_to_bv 5 22) = Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 22)) + 16) ->
  getr regs' (Z_to_bv 5 27) = Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 27)) + 1) ->
  Z.of_nat c < 32 -> um_mk cx + MK_SIZE + 8 <= 2 ^ 63 -> 0 < um_mk cx ->
  urb_R cx fpos (S c) regs'.
Proof.
  intros c regs regs' (R2 & R9 & R8 & R18 & R19 & R25 & R20 & R3 & R4 & R21 & R22 & R23 & R24 & R26 & R27)
    CS Q22 Q27 Hc Hmk Hm0.
  assert (K : forall r, acallee_saved r -> r <> 22 -> r <> 27 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by exact CS.
  unfold urb_R.
  split; [exact (eq_trans (K 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R2)|].
  split; [exact (eq_trans (K 9 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R9)|].
  split; [exact (eq_trans (K 8 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R8)|].
  split; [exact (eq_trans (K 18 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R18)|].
  split; [exact (eq_trans (K 19 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R19)|].
  split; [exact (eq_trans (K 25 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R25)|].
  split; [exact (eq_trans (K 20 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R20)|].
  split; [exact (eq_trans (K 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R3)|].
  split; [exact (eq_trans (K 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R4)|].
  split; [exact (eq_trans (K 21 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R21)|].
  split.
  { refine (eq_trans Q22 _).
    rewrite (urd_bvu (getr regs (Z_to_bv 5 22)) _ R22) by (unfold MK_NAME, MARK_LEN, MK_SIZE in *; lia).
    unfold w64. f_equal. rewrite Nat2Z.inj_succ. unfold MARK_LEN. lia. }
  split; [exact (eq_trans (K 23 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R23)|].
  split; [exact (eq_trans (K 24 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R24)|].
  split; [exact (eq_trans (K 26 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) R26)|].
  refine (eq_trans Q27 _).
  rewrite (urd_bvu (getr regs (Z_to_bv 5 27)) _ R27) by lia.
  unfold w64. f_equal. lia.
Qed.
End c.

(* ==========================================================================
   THE PIECE: JOIN c -> HEAD (S c) / TAIL
   ========================================================================== *)
Theorem um_join : um_tail_obl SK B -> forall c, um_head_obl SK B (S c) -> um_join_obl SK B c.
Proof.
intros HTAIL c HHEAD cx fpos ly3 S3 W3 ms3 md3 HPRE HGI.
destruct HGI as (Hpc & HLOOP & (kbs & HKI) & HBASE).
pose proof HBASE as HBASE0. pose proof HLOOP as HLOOP0.
destruct HBASE as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & HJ3 & Hfrs3 & Hnin & HfsS3 & Hperm & HS1W & Hfa3
  & R2 & R9 & R8 & R18 & R19 & R25 & R20 & R3 & R4 & _ & _ & _ & HFpres & HSpres & _ & Hfds3 & Hfs3 & _).
destruct HLOOP as (Hm & Hc & R21 & R22 & R23 & R24 & R26 & R27 & _ & _ & Hmk3).
pose proof (urb_R_of SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c ly3 S3 W3 ms3 md3 HLOOP0 HBASE0) as RR3.
pose proof (rk_inv_of_base SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c ly3 S3 W3 ms3 md3 HBASE0 HLOOP0)
  as HINV3.
destruct (rk_win SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W)
  as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & S1al16).
destruct (rk_F SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (rk_SH SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W) as (SH1 & SH2 & SH3 & SH4).
destruct (rk_mk SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W Hm) as (M0 & M1 & _ & _ & _ & _ & _ & MA & MW).
pose proof MW as (MR & _). unfold MARKS_MAX in MR.
pose proof HPRE as ((HJ & HGX & _) & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HmF : ~ (um_F cx fpos <= um_mk cx < um_F cx fpos + 512)).
{ intros HH. apply (rk_mk_not_side SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W (um_mk cx) Hm
    ltac:(unfold MK_SIZE; lia)).
  apply (proj2 (rk_side_unfold SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W (um_mk cx))). left. exact HH. }
pose proof (jn_mk_sh0 cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms3) md3 HJ3 HINV3) as SH0.
assert (Hn32 : 0 <= um_n cx <= 32) by (unfold um_n; lia).
(* ---- the environment ---- *)
pose (E := jn_env (ms_regs ms3) (um_gbs cx)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hr; exact (jn_ew (ms_regs ms3) (um_gbs cx) n r Hr)).
assert (ED : ed E 0 = um_gbs cx) by reflexivity.
assert (U18 : bv_unsigned (ew E 18) = um_SH cx fpos).
{ rewrite (EREG 18%nat 18%bv eq_refl), R18. unfold w64. apply unsigned_lit_small.
  unfold SHADOW_OFF, kHighMemBeg in *. lia. }
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF + um_mk cx / 8).
{ rewrite (EREG 26%nat 26%bv eq_refl), R26. unfold w64. apply unsigned_lit_small.
  unfold amem_range, MK_SIZE, SHADOW_OFF, kHighMemEnd, kLowMemEnd in *. lia. }
assert (U20 : bv_unsigned (ew E 20) = um_mk cx).
{ rewrite (EREG 20%nat 20%bv eq_refl), R20. reflexivity. }
assert (U27 : bv_unsigned (ew E 27) = Z.of_nat c).
{ rewrite (EREG 27%nat 27%bv eq_refl), R27. unfold w64. apply unsigned_lit_small. lia. }
assert (DW : data_word E 0 0 4 = um_n cx).
{ unfold data_word. rewrite ED. reflexivity. }
(* the marks block's count bytes at the cut *)
destruct MA as [[MB _] ML].
assert (HMN : forall i, 0 <= i < 4 -> exists b, nth_error (um_gbs cx) (Z.to_nat i) = Some b /\
  mbyte SEGS (rdW W3 (ms_mem ms3)) (um_mk cx + i) = Some b).
{ intros i Hi. destruct MB as (_ & _ & MBb).
  destruct (nth_error (um_gbs cx) (Z.to_nat i)) as [b|] eqn:Eb.
  - exists b. split; [reflexivity|].
    rewrite (YCbq.mbyte_of_aview SEGS (w_H (um_W cx)) (w_H W3) (um_memc cx) (ms_mem ms3) (um_mk cx + i))
      by (apply Hmk3; unfold MK_SIZE; lia).
    replace (um_mk cx + i) with (um_mk cx + Z.of_nat (Z.to_nat i)) by lia.
    rewrite <- Eb. exact (MBb (Z.to_nat i) ltac:(unfold MK_SIZE in ML; lia)).
  - exfalso. apply nth_error_None in Eb. unfold MK_SIZE in ML. lia. }
(* ---- the symbolic state at JOIN ---- *)
assert (HS : st_ok_pi SEGS VAL E jn_ss0 (restrict (w_H W3) ms3)).
{ rewrite (urd_ms_eta ms3 Zfrg Zsvc Zrsv Zfcsr), Hpc, Zrom, restrict_mkst_fx.
  unfold jn_ss0, w64. apply pa_entry_st_ok_full.
  - apply jn_regs_ok.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok, jn_SHR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18.
      split; [unfold SHADOW_OFF, kHighMemBeg in *; lia|]. split; [unfold SHADOW_OFF, kHighMemBeg in *; lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (YCbq.apresent_writable SEGS). apply HSpres. unfold UM_SHN. lia.
    + unfold region_ok, jn_MSH.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U26.
      split; [unfold SHADOW_OFF; lia|].
      split; [unfold amem_range, MK_SIZE, SHADOW_OFF, kHighMemEnd, kLowMemEnd in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. apply jn_chunk_zero. exact SH0.
    + unfold region_ok, jn_MN.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
      split; [lia|]. split; [unfold amem_range, MK_SIZE, kHighMemEnd, kLowMemEnd in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. exact (jn_chunk_data E _ _ (um_gbs cx) ED HMN).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val jn_SHR jn_MSH jn_MN]. rewrite U18, U26, U20.
    unfold amem_range, MK_SIZE in M1. rewrite SH1.
    unfold SHADOW_OFF, kHighMemBeg, kHighMemEnd, kLowMemEnd in *.
    repeat split; try exact I; lia.
  - split; [|split; [exact I | exact I]]. cbn [jn_facts f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U18. change (2 ^ 3) with 8.
    unfold SHADOW_OFF, kHighMemBeg, kLowMemEnd in *. repeat split; lia. }
assert (HE : E = jn_env (ms_regs ms3) (um_gbs cx)) by reflexivity.
clearbody E.
(* ---- the run +0x294 .. +0x328: the 32 shadow stores, m's shadow byte, m->n, the two increments ---- *)
pose proof (paj_run_plain_x SK B LAWS (um_G cx) HGX (um_XO cx) (um_OUT cx)) as RUN.
pose proof (paj_run_to_plain_x SK B LAWS (um_G cx) HGX (um_XO cx) (um_OUT cx)) as RUNTO.
urj_run RUN HS HJ3.
{ intros a (r & Hr & Ha). urj_wr Hr Ha U18. left.
  apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UM_CID fpos a HJ3
    ltac:(left; reflexivity)).
  right. unfold in_zr. cbn [fst snd]. rewrite Hfa3. change (fs_frame_bytes UM_CID / 8) with 64.
  unfold um_SH, um_F in Ha. unfold shadow_addr. lia. }
intros ms1 mat1 HS1 HJ1 HFr1 HFr1' HG1.
set (md1 := with_vm_backing (m_vm_lazy md3) mat1 md3) in *.
destruct (urd_wvb_fds_fs (m_vm_lazy md3) mat1 md3) as (Efds1 & Efs1).
assert (UN1 : forall a, 0 <= a < 2 ^ 64 -> ~ (um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn. apply (YCbq.aview_eq_of SEGS). apply HFr1'. rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hra). urj_wr Hr Hra U18. apply Hn. lia. }
assert (HX : forall a, um_SH cx fpos + 4 <= a < um_SH cx fpos + 36 ->
  (um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= a < um_sp1 cx) \/ (um_SH cx fpos <= a < um_SH cx fpos + 64))
  by (intros a Ha; right; lia).
assert (HINV1 : rk_inv SK B cx fpos ly3 S3 W3 (ms_mem ms1) md1).
{ apply (rk_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms3) md3 (ms_mem ms1) md1
    (fun a => um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) HINV3 HJ1 UN1 HX).
  - intros a Hp. exact (urd_apresent_grows (w_H W3) (ms_mem ms3) (ms_mem ms1) a HG1 Hp).
  - exact Efds1.
  - exact Efs1. }
pose proof (rk_kinv_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms3) md3 (ms_mem ms1)
  (fun a => um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) kbs (S c) HINV3 UN1 HX HKI) as HKI1.
(* ---- +0x328: blt s11, a0 ---- *)
apply (paj_branch W3 E _ ms1 md1 _ BC_LT (SOff 27 1) (SExt true 32 (SData 0 0 4)) HS1).
- (* ==== c + 1 < n: HEAD, round c + 1 ==== *)
  intros Hbt HSt. rewrite (jn_blt E (Z.of_nat c) (um_n cx) U27 DW ltac:(lia) Hn32) in Hbt.
  apply Z.ltb_lt in Hbt.
  urb_run_to RUNTO HSt HJ1 UM_CUT_HEAD.
  { intros a (r & Hr & Ha). urj_wr Hr Ha U18. left.
    apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UM_CID fpos a HJ1
      ltac:(left; reflexivity)).
    right. unfold in_zr. cbn [fst snd]. rewrite Hfa3. change (fs_frame_bytes UM_CID / 8) with 64.
    unfold um_SH, um_F in Ha. unfold shadow_addr. lia. }
  intros msH matH HSH HJH HFH HFH' HGH.
  set (mdH := with_vm_backing (m_vm_lazy md1) matH md1) in *.
  destruct (urd_wvb_fds_fs (m_vm_lazy md1) matH md1) as (EfdsH & EfsH).
  assert (UNH : forall a, 0 <= a < 2 ^ 64 -> ~ (um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) ->
    aview SEGS (w_H W3) (ms_mem msH) a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha Hn. apply (YCbq.aview_eq_of SEGS). apply HFH'. rewrite unsigned_lit_small by lia.
    intros (r & Hr & Hra). urj_wr Hr Hra U18. apply Hn. lia. }
  assert (HINVH : rk_inv SK B cx fpos ly3 S3 W3 (ms_mem msH) mdH).
  { apply (rk_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1 (ms_mem msH) mdH
      (fun a => um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) HINV1 HJH UNH HX).
    - intros a Hp. exact (urd_apresent_grows (w_H W3) (ms_mem ms1) (ms_mem msH) a HGH Hp).
    - exact EfdsH.
    - exact EfsH. }
  pose proof (rk_kinv_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1
    (ms_mem msH) (fun a => um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) kbs (S c) HINV1 UNH HX HKI1) as HKIH.
  pose proof HSH as HSH'. rewrite HE in HSH'.
  pose proof (jn_cs (w_H W3) (ms_regs ms3) (um_gbs cx) _ msH HSH' ltac:(urj_cs_tac)) as CSH.
  pose proof (jn_reg (w_H W3) (ms_regs ms3) (um_gbs cx) _ msH 22 16 HSH' ltac:(lia) ltac:(vm_compute; reflexivity)) as Q22.
  pose proof (jn_reg (w_H W3) (ms_regs ms3) (um_gbs cx) _ msH 27 1 HSH' ltac:(lia) ltac:(vm_compute; reflexivity)) as Q27.
  pose proof (jn_R_next cx fpos HPRE Hnin HS1W c (ms_regs ms3) (ms_regs msH) RR3 CSH Q22 Q27 ltac:(lia)
    ltac:(unfold amem_range, MK_SIZE, kHighMemEnd, kLowMemEnd in *; lia) M0) as RRH.
  pmkst HSH.
  apply (HHEAD cx fpos ly3 S3 W3 _ mdH HPRE).
  destruct (urb_close SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W (S c) ly3 S3 W3 (ms_regs msH)
    (Z_to_bv 64 (BASE + UM_CUT_HEAD)) (ms_mem msH) mdH ltac:(rewrite Nat2Z.inj_succ; lia) RRH HINVH) as (HLH & HBH).
  unfold um_gi_head. cbn [ms_pc_val ms_regs ms_mem mkst].
  split; [unfold w64, UM_CUT_HEAD, AF_reac_served_unmark_all; reflexivity|].
  split; [exact HLH|]. split; [exists kbs; exact HKIH | exact HBH].
- (* ==== c + 1 = n: TAIL ==== *)
  intros Hbf HSf. rewrite (jn_blt E (Z.of_nat c) (um_n cx) U27 DW ltac:(lia) Hn32) in Hbf.
  apply Z.ltb_ge in Hbf.
  urb_run_to RUNTO HSf HJ1 UM_CUT_TAIL.
  { intros a (r & Hr & Ha). urj_wr Hr Ha U18. left.
    apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UM_CID fpos a HJ1
      ltac:(left; reflexivity)).
    right. unfold in_zr. cbn [fst snd]. rewrite Hfa3. change (fs_frame_bytes UM_CID / 8) with 64.
    unfold um_SH, um_F in Ha. unfold shadow_addr. lia. }
  intros msT matT HST HJT HFT HFT' HGT.
  set (mdT := with_vm_backing (m_vm_lazy md1) matT md1) in *.
  destruct (urd_wvb_fds_fs (m_vm_lazy md1) matT md1) as (EfdsT & EfsT).
  assert (UNT : forall a, 0 <= a < 2 ^ 64 -> ~ (um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) ->
    aview SEGS (w_H W3) (ms_mem msT) a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha Hn. apply (YCbq.aview_eq_of SEGS). apply HFT'. rewrite unsigned_lit_small by lia.
    intros (r & Hr & Hra). urj_wr Hr Hra U18. apply Hn. lia. }
  assert (HINVT : rk_inv SK B cx fpos ly3 S3 W3 (ms_mem msT) mdT).
  { apply (rk_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1 (ms_mem msT) mdT
      (fun a => um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) HINV1 HJT UNT HX).
    - intros a Hp. exact (urd_apresent_grows (w_H W3) (ms_mem ms1) (ms_mem msT) a HGT Hp).
    - exact EfdsT.
    - exact EfsT. }
  pose proof (rk_kinv_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1
    (ms_mem msT) (fun a => um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) kbs (S c) HINV1 UNT HX HKI1) as HKIT.
  pose proof HST as HST'. rewrite HE in HST'.
  pose proof (jn_cs (w_H W3) (ms_regs ms3) (um_gbs cx) _ msT HST' ltac:(urj_cs_tac)) as CST.
  pose proof (jn_reg (w_H W3) (ms_regs ms3) (um_gbs cx) _ msT 22 16 HST' ltac:(lia) ltac:(vm_compute; reflexivity)) as Q22.
  pose proof (jn_reg (w_H W3) (ms_regs ms3) (um_gbs cx) _ msT 27 1 HST' ltac:(lia) ltac:(vm_compute; reflexivity)) as Q27.
  pose proof (jn_R_next cx fpos HPRE Hnin HS1W c (ms_regs ms3) (ms_regs msT) RR3 CST Q22 Q27 ltac:(lia)
    ltac:(unfold amem_range, MK_SIZE, kHighMemEnd, kLowMemEnd in *; lia) M0)
    as (T2 & T9 & T8 & T18 & T19 & T25 & T20 & T3 & T4 & _).
  pose proof HINVT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HmkT).
  pmkst HST.
  apply (HTAIL cx fpos ly3 S3 W3 _ mdT HPRE).
  unfold um_gi_tail. cbn [ms_pc_val ms_regs ms_mem mkst].
  split; [unfold w64, UM_CUT_TAIL, AF_reac_served_unmark_all; reflexivity|].
  split; [exact Hm|]. split; [exact HmkT|].
  split.
  { exists kbs. replace (Z.to_nat (um_n cx)) with (S c) by lia. exact HKIT. }
  apply (rk_base_of_inv SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 _ mdT);
    cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]; first [reflexivity | assumption].
Qed.
End b.
End a.
