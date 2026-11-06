(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 12453 of its 12546 lines of code are new or changed and 1136 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/drain_b.v, with its module paths and module names changed; 874 of its 974 lines of code are new or changed and 12446 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04 YO0x YO10 YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memcpy_c __errno_location_c send_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB send_line_loop send_line_seg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_glue send_line_b_m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sr_in_mid : forall {T} (b1 b2 : list T) x y, In x (b1 ++ y :: b2) -> x <> y -> In x (b1 ++ b2).
Proof.
  intros T b1 b2 x y H N. apply in_app_or in H. apply in_or_app.
  destruct H as [H|[H|H]]; [left; exact H | congruence | right; exact H].
Qed.

Lemma sr_mid_eq : forall {T} (b1 b2 c1 c2 : list T) x, b1 ++ x :: b2 = c1 ++ x :: c2 ->
  ~ In x b1 -> ~ In x c1 -> b1 = c1 /\ b2 = c2.
Proof.
  intros T b1. induction b1 as [|y b1 IH]; intros b2 c1 c2 x E N1 N2; destruct c1 as [|z c1].
  - cbn in E. inversion E; subst. split; reflexivity.
  - cbn in E. inversion E; subst. exfalso. apply N2. left. reflexivity.
  - cbn in E. inversion E; subst. exfalso. apply N1. left. reflexivity.
  - cbn in E. injection E as E1 E2. subst z.
    destruct (IH b2 c1 c2 x E2) as [-> ->];
      [intros H; apply N1; right; exact H | intros H; apply N2; right; exact H |].
    split; reflexivity.
Qed.

Lemma sr_cb : forall m a bs, bytes_at rsegs m a bs -> (forall i, 0 <= i < Z.of_nat (length bs) -> present m (a + i)) ->
  rw_cells rsegs m a [CB (length bs) bs].
Proof.
  intros m a bs HB HP. pose proof (bytes_at_bound rsegs m a bs HB) as BB.
  split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct (HP i ltac:(lia)) as [b E]. unfold wview, wa. rewrite E. discriminate.
Qed.

(* A disjunction that lia does not unfold: lia splits every disjunctive hypothesis in its context. *)
Definition SrOr (P Q : Prop) : Prop := P \/ Q.

Ltac lc := repeat match goal with H : _ \/ _ |- _ => clear H end; lia.

Section SB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis BW : blocks_writable Bm API.
Hypothesis EU : errno_unowned Bm API.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTXO : ctx_owned Bm API.
Hypothesis NODUP : blocks_nodup Bm API.

Lemma sr_rp_mono : forall K (E E' F F' : Z -> Prop) L A R m md L' A' R' m' md',
  relay_post Bm API K E F L A R m md L' A' R' m' md' -> (forall a, E a -> E' a) -> (forall q, F q -> F' q) ->
  relay_post Bm API K E' F' L A R m md L' A' R' m' md'.
Proof using.
  intros K E E' F F' L A R m md L' A' R' m' md' P HE HF.
  destruct P as (M1 & W1 & B1 & LL1 & LN1 & AD1 & SV1 & Z1 & OW1 & RP1 & MD1 & FR1 & BY1 & SC1).
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact LL1|]. split; [exact LN1|].
  split; [intros p n H1 H2 NF; apply (AD1 p n H1 H2); intros X; apply NF, HF, X|].
  split; [intros p n H1 Hn NF; apply (SV1 p n H1 Hn); intros X; apply NF, HF, X|].
  split; [exact Z1|]. split; [exact OW1|]. split; [exact RP1|]. split; [exact MD1|].
  split; [intros a Ha N1 N2 NS NE; apply FR1; [exact Ha | exact N1 | exact N2 | exact NS | intros X; apply NE, HE, X]|].
  split; [intros p n i H1 H2 NF Hi NE; apply (BY1 p n i H1 H2);
          [intros X; apply NF, HF, X | exact Hi | intros X; apply NE, HE, X]|].
  exact SC1.
Qed.

Set Default Proof Using "All".

Section Main.
Variable RF : ResFormT.
Hypothesis MC : memcpy_contract.
Hypothesis EL : __errno_location_contract.
Hypothesis RA : realloc_contract_rt Bm API RF 0x178f8.
Hypothesis RN : realloc_null_contract_rt Bm API RF 0x178f8.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (bnd : rt_R RF)
  (Bl O junk : list byte) (cl br dd ei : Z) (mx nout cap out ev : word).
Local Abbreviation SP := (bv_unsigned (getr regs 2)).
Local Abbreviation LINE := (bv_unsigned (getr regs 10)).
Local Abbreviation LEN := (bv_unsigned (getr regs 11)).
Local Abbreviation ERR := (errno_addr Bm).
Local Abbreviation NO := (bv_unsigned nout).
Local Abbreviation CAP := (bv_unsigned cap).
Local Abbreviation OUT := (bv_unsigned out).
Local Abbreviation live := (send_live cl br dd LEN).
Local Abbreviation off := (send_off cl br LEN).
Local Abbreviation EE := (send_writes live OUT CAP).
Local Abbreviation FF := (fun q => live = true /\ q = OUT).
Local Abbreviation SLTR := (send_line_tr (send_live cl br dd (bv_unsigned (getr regs 11))) (bv_unsigned mx)
  (bv_unsigned nout) (bv_unsigned cap) (bv_unsigned (getr regs 11)) 0 (known_at L A (bv_unsigned out))).
Hypothesis H01 : ms_segs Bm = rsegs.
Hypothesis H02 : call_pre_k Bm (aa_MR API) SEND_LINE_K L A regs mem md.
Hypothesis H03 : st_init_done A = true.
Hypothesis H04 : ms_tp Bm + ERRNO_OFF = ERR.
Hypothesis H04a : ERR mod 4 = 0.
Hypothesis H05 : G_RELAY_HI <= ERR.
Hypothesis H06 : ro_agree (ms_segs Bm) mem.
Hypothesis H07 : bytes_at (ms_segs Bm) mem LINE Bl.
Hypothesis H08 : Z.of_nat (length Bl) = LEN.
Hypothesis H09 : LINE + LEN <= G_RELAY_LO \/ G_RELAY_HI <= LINE.
Hypothesis H10 : LINE + LEN <= ERR \/ ERR + 4 <= LINE.
Hypothesis H11 : LINE + LEN <= SP - SEND_LINE_K \/ SP <= LINE.
Hypothesis H12 : forall a, G_RELAY_LO <= a < G_RELAY_HI -> img_plain Bm a.
Hypothesis H13 : forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a.
Hypothesis H14 : forall a, ERR <= a < ERR + 4 -> in_img Bm a.
Hypothesis H15 : (forall a, LINE <= a < LINE + LEN -> img_plain Bm a) \/
  (exists q k, In (q, k) (blocks L A) /\ q <= LINE /\ LINE + LEN <= q + k /\ q <> OUT).
Hypothesis H16 : cl = 3 \/ cl = -1.
Hypothesis H17 : br = 0 \/ br = 1.
Hypothesis H18 : dd = 0 \/ dd = 1.
Hypothesis H19 : ei = 0 \/ ei = 1.
Hypothesis H20 : rw_cells (ms_segs Bm) mem G_CLIENT [C4 (Z_to_bv 64 cl)].
Hypothesis H21 : rw_cells (ms_segs Bm) mem G_BROKEN [C1 (Z_to_bv 8 br)].
Hypothesis H22 : rw_cells (ms_segs Bm) mem G_DEAD [C1 (Z_to_bv 8 dd)].
Hypothesis H23 : rw_cells (ms_segs Bm) mem G_EINTR [C1 (Z_to_bv 8 ei)].
Hypothesis H24 : rw_cells (ms_segs Bm) mem G_OUTV [C8 mx; C8 nout; C8 cap; C8 out].
Hypothesis H25 : rw_cells (ms_segs Bm) mem ERR [C4 ev].
Hypothesis H26 : (CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
  (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L A) /\ fresh_block Bm OUT CAP /\
   bytes_at (ms_segs Bm) mem OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO /\
   (LINE + LEN <= OUT \/ OUT + CAP <= LINE)).
Hypothesis H27 : 2 * (NO + LEN) < 2 ^ 63.
Hypothesis H28 : rt_ok RF A bnd.
Hypothesis H29 : forall qs, length qs = nretF SLTR -> roomF RF qs bnd SLTR.
Hypothesis HMPC : ms_malloc Bm = 0x1608c.

Local Abbreviation XA f := (f Bm API BW EU AX CTXO RF MC EL RA RN L A regs mem md bnd Bl O junk cl br dd ei mx nout cap
  out ev H01 H02 H03 H04 H04a H05 H06 H07 H08 H09 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26
  H27 H28 H29) (only parsing).
Local Abbreviation SPOST := (sb_post Bm API RF L A regs mem md bnd Bl O cl br dd ei mx nout cap out ev).
Local Abbreviation SBLK := (sb_blk Bm L A regs nout cap out).
Local Abbreviation SCALL := (sb_call Bm API RF L A regs mem md bnd Bl O cl br dd mx nout cap out).
Local Abbreviation SRES := (sb_res RF L A regs bnd cl br dd mx nout cap out).
Local Abbreviation SCREGS := (sb_cregs regs).

(* The UBSAN checks of send_line need errno aligned, a nonzero line and a nonzero buffer. *)
Lemma sr_hem : (bv_unsigned (reg_get regs 4) + -164) mod 4 = 0.
Proof using All. rewrite (XA sb_etp). exact H04a. Qed.

Lemma sr_hl0 : 0 < bv_unsigned (reg_get regs 11) -> 0 < bv_unsigned (reg_get regs 10).
Proof using All.
  intros LP.
  pose proof (zr_word (getr regs 10)) as Rl. pose proof (zr_word (getr regs 11)) as Rn. unfold inr64 in *.
  assert (HIN : LINE <= LINE < LINE + LEN) by (split; [apply Z.le_refl | apply Z.lt_add_pos_r; exact LP]).
  destruct H15 as [IMG|(q & kq & INq & Q1 & Q2 & NQ)].
  - pose proof (sb_img_pos Bm H01 _ (proj1 (IMG LINE HIN))) as P4.
    change (bv_unsigned (reg_get regs 10)) with LINE. lia.
  - pose proof H02 as (HM & _).
    unfold blocks in INq. apply in_map_iff in INq as ([p k'] & E & Hp). cbn [fst snd] in E. injection E as Ep Ek.
    subst k'.
    assert (Kp : 0 <= 0 < kq) by (change (bv_unsigned (reg_get regs 11)) with LEN in LP; lia).
    destruct (mr_blocks Bm _ (aa_laws API) L A mem md p kq 0 HM Hp Kp) as (_ & H4 & _).
    change (bv_unsigned (reg_get regs 10)) with LINE. lia.
Qed.

Lemma sr_hop : 0 < CAP -> 0 < OUT.
Proof using All.
  intros Cp. destruct H26 as [(C0 & _)|(_ & _ & _ & (F1 & _) & _)]; lia.
Qed.

(* The state reached when realloc returns to send_line, for either form of the call: the request is
   realloc (NULL, n) when cap1 = 0, else of the cap1-byte block, whose model pointer is p; q is the new block's. *)
Definition sr_rl (b : rt_R RF) (p : sptr) (cap1 out1 : word) (n : Z) (old : list byte) (L1 : layout) (A1 : astate)
    (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) (c' : config) : Prop :=
  exists L2 A2 regs2 mem2 md2 res,
    c' = mkCfg (YK11.mkst regs2 (getr regs1 1) mem2 (seg_rom rsegs)) md2 /\
    relay_post Bm API REALLOC_STACK (fun a => bv_unsigned out1 <= a < bv_unsigned out1 + bv_unsigned cap1)
      (fun q => q = bv_unsigned out1) L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 /\
    getr regs2 10 = Z_to_bv 64 res /\ res <> 0 /\ fresh_block Bm res n /\
    (exists b1 b2 c1 c2, blocks L2 A2 = c1 ++ (res, n) :: c2 /\ c1 ++ c2 = b1 ++ b2 /\
       ((bv_unsigned cap1 = 0 /\ blocks L1 A1 = b1 ++ b2) \/
        (0 < bv_unsigned cap1 /\ blocks L1 A1 = b1 ++ (bv_unsigned out1, bv_unsigned cap1) :: b2))) /\
    ro_agree rsegs mem2 /\ bytes_at rsegs mem2 res old /\
    st_init_done A2 = true /\
    exists q, live_at L2 A2 q res n /\
      rt_ok RF A2 (if bv_unsigned cap1 =? 0 then rt_malloc RF b n else rt_realloc RF b (bv_unsigned cap1) n p q).

Lemma sr_rl_ra : forall L1 A1 regs1 mem1 md1 b p (cap1 out1 : word) n old,
  call_pre_k Bm (aa_MR API) REALLOC_STACK L1 A1 regs1 mem1 md1 -> ro_agree rsegs mem1 ->
  0 < bv_unsigned cap1 -> live_at L1 A1 p (bv_unsigned out1) (bv_unsigned cap1) ->
  getr regs1 10 = out1 -> getr regs1 11 = Z_to_bv 64 n -> bv_unsigned cap1 < n ->
  bytes_at rsegs mem1 (bv_unsigned out1) old -> Z.of_nat (length old) = bv_unsigned cap1 ->
  rt_ok RF A1 b -> rt_room RF b n ->
  SR rsegs (mkCfg (YK11.mkst regs1 (Z_to_bv 64 0x178f8) mem1 (seg_rom rsegs)) md1)
    (sr_rl b p cap1 out1 n old L1 A1 regs1 mem1 md1).
Proof using All.
  intros L1 A1 regs1 mem1 md1 b p cap1 out1 n old PRE RO1 Cp [Hp Ep] E10 E11 LT OB LOLD RES ROOM.
  pose proof PRE as (HM1 & HW1 & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof (bytes_at_bound rsegs mem1 _ _ OB) as BOB.
  assert (A10 : getr regs1 10 = Z_to_bv 64 (ptr_addr L1 p)) by (rewrite Ep, Z_to_bv_lit_self; exact E10).
  assert (AOLD : forall i, 0 <= i < bv_unsigned cap1 ->
            mbyte rsegs mem1 (ptr_addr L1 p + i) = nth_error old (Z.to_nat i)).
  { intros i Hi. rewrite Ep. pose proof (mbyte_of_bytes_at rsegs mem1 _ _ (Z.to_nat i) OB ltac:(lia)) as X.
    rewrite Z2Nat.id in X by lia. exact X. }
  pose proof RA as R. unfold realloc_contract_rt in R. rewrite H01 in R.
  eapply SR_mono; [exact (R L1 A1 regs1 mem1 md1 p (bv_unsigned cap1) n old b PRE RO1 Hp A10 E11
                            AOLD LOLD RES ROOM)|].
  intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & CP & A0 & NZ & AL & FR & BLK & KEPT & RO2 & GK & SURV & CPY
             & INI2 & LN & q & Hq & Eq & RES2).
  assert (N0 : 0 <= n) by lia.
  pose proof FR as (F1 & F2 & _).
  exists L2, A2, regs2, mem2, md2, res. split; [reflexivity|].
  split.
  { pose proof (sb_realloc_rp Bm API AX CTXO L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 p (bv_unsigned cap1)
                  HW1 Hp Cp HM1 CP SURV LN) as RP.
    rewrite Ep in RP. exact RP. }
  split; [exact A0|]. split; [exact NZ|]. split; [exact FR|].
  split.
  { destruct BLK as (b1 & b2 & c1 & c2 & E1 & E2 & E3). rewrite Ep in E1.
    exists b1, b2, c1, c2. split; [exact E2|]. split; [exact E3|]. right. split; [exact Cp | exact E1]. }
  split; [exact RO2|].
  split.
  { apply bytes_at_of_mbyte; [lia | lia |].
    intros i Hi. rewrite (CPY (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity. }
  split; [exact INI2|].
  exists q. split; [split; [exact Hq | exact Eq]|].
  rewrite (proj2 (Z.eqb_neq (bv_unsigned cap1) 0)) by lia. exact RES2.
Qed.

Lemma sr_rl_rn : forall L1 A1 regs1 mem1 md1 b p (cap1 out1 : word) n old,
  call_pre_k Bm (aa_MR API) REALLOC_STACK L1 A1 regs1 mem1 md1 -> ro_agree rsegs mem1 ->
  bv_unsigned cap1 = 0 -> bv_unsigned out1 = 0 ->
  getr regs1 10 = out1 -> getr regs1 11 = Z_to_bv 64 n -> old = [] -> 0 <= n ->
  getr regs1 1 <> Z_to_bv 64 (ms_malloc Bm) ->
  rt_ok RF A1 b -> rt_room RF b n ->
  SR rsegs (mkCfg (YK11.mkst regs1 (Z_to_bv 64 0x178f8) mem1 (seg_rom rsegs)) md1)
    (sr_rl b p cap1 out1 n old L1 A1 regs1 mem1 md1).
Proof using All.
  intros L1 A1 regs1 mem1 md1 b p cap1 out1 n old PRE RO1 C0 O0 E10 E11 -> N0 RNM RES ROOM.
  pose proof PRE as (HM1 & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (A10 : getr regs1 10 = Z_to_bv 64 0).
  { transitivity out1; [exact E10|]. rewrite <- (Z_to_bv_lit_self out1). rewrite O0. reflexivity. }
  pose proof RN as R. unfold realloc_null_contract_rt, malloc_ret_rt in R. rewrite H01 in R.
  eapply SR_mono; [exact (R L1 A1 regs1 mem1 md1 n b PRE RO1 A10 E11 RNM RES ROOM)|].
  intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & CP & A0 & NZ & AL & FR & (b1 & b2 & E1 & E2) & KEPT & RO2
             & GK & SURV & INI2 & LN & RES2).
  pose proof FR as (F1 & F2 & _).
  assert (RP : relay_post Bm API REALLOC_STACK (fun a => bv_unsigned out1 <= a < bv_unsigned out1 + bv_unsigned cap1)
      (fun q => q = bv_unsigned out1) L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2).
  { apply (sr_rp_mono _ (fun _ => False) _ (fun _ => False));
      [exact (sb_null_rp Bm API AX CTXO L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 HM1 CP SURV LN)
      | intros a [] | intros q []]. }
  pose proof RP as (M2 & _).
  exists L2, A2, regs2, mem2, md2, res. split; [reflexivity|].
  split; [exact RP|].
  split; [exact A0|]. split; [exact NZ|]. split; [exact FR|].
  split.
  { exists b1, b2, b1, b2. split; [exact E1|]. split; [reflexivity|]. left. split; [exact C0 | exact E2]. }
  split; [exact RO2|].
  split.
  { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
  split; [exact INI2|].
  assert (INB : In (res, n) (blocks L2 A2)) by (rewrite E1; apply in_or_app; right; left; reflexivity).
  destruct (sptr_of_spec L2 A2 res n (NODUP L2 A2 mem2 md2 M2) INB) as [Hq Eq].
  exists (sptr_of L2 A2 res). split; [split; [exact Hq | exact Eq]|].
  rewrite (proj2 (Z.eqb_eq (bv_unsigned cap1) 0) C0). exact RES2.
Qed.

Lemma sr_pre : forall L1 A1 regs1 mem1 md1 k nk1 out1 c1,
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs mem1 md1 -> st_init_done A1 = true ->
  SCREGS regs1 k nk1 out1 c1 ->
  call_pre_k Bm (aa_MR API) REALLOC_STACK L1 A1 regs1 mem1 md1.
Proof using All.
  intros L1 A1 regs1 mem1 md1 k nk1 out1 c1 RP1 INI1 CR.
  pose proof (XA sb_sp) as (S1 & S2 & S3 & S4).
  pose proof H02 as (_ & _ & _ & _ & _ & _ & _ & _ & HTP & _).
  destruct RP1 as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  destruct CR as (E1 & E2 & E3 & E4 & _).
  assert (SPE : spZ regs = SP) by reflexivity.
  assert (SPR : spZ regs1 = SP - 112).
  { unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 (SP + -112))); [f_equal; exact E2|]. apply unsigned_lit. lia. }
  assert (RA1 : YK0s.ret_ok (getr regs1 1)) by (rewrite E1; apply ret_ok_even; vm_compute; reflexivity).
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact RA1|].
  split; [rewrite SPR; Z.div_mod_to_equations; lia|].
  split; [rewrite SPR; unfold REALLOC_STACK, ALLOC_STACK; lia|].
  split; [rewrite SPR; lia|].
  split.
  { intros a Ha. rewrite SPR in Ha. unfold REALLOC_STACK, ALLOC_STACK in Ha. apply SC1. left. rewrite SPE.
    unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK. lia. }
  split; [exact (eq_trans E4 HTP)|].
  split; [intros a Ha; apply SC1; right; exact Ha|].
  intros X. rewrite INI1 in X. discriminate.
Qed.

Lemma sr_keep : forall L1 A1 regs1 mem1 md1 L2 A2 R2 m2 md2 (out1 cap1 : word) a,
  aa_MR API L1 A1 mem1 md1 ->
  relay_post Bm API REALLOC_STACK (fun x => bv_unsigned out1 <= x < bv_unsigned out1 + bv_unsigned cap1)
    (fun q => q = bv_unsigned out1) L1 A1 regs1 mem1 md1 L2 A2 R2 m2 md2 ->
  spZ regs1 = SP - 112 ->
  (forall x, bv_unsigned out1 <= x < bv_unsigned out1 + bv_unsigned cap1 -> x < YM05.alloc_ceiling /\ ~ in_img Bm x) ->
  ((SP - 112 <= a < SP) \/ img_plain Bm a) ->
  mbyte rsegs m2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a -> writable_at rsegs m2 a).
Proof using All.
  intros L1 A1 regs1 mem1 md1 L2 A2 R2 m2 md2 out1 cap1 a HM1 RP2 SPR HE2 HA.
  destruct RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR2 & _).
  pose proof (XA sb_tp) as (TP1 & TP2 & TP3). pose proof (XA sb_sp) as (S1 & S2 & S3 & S4).
  assert (K : (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) /\ ~ owned Bm L1 A1 a /\ ~ owned Bm L2 A2 a /\
              ~ scratch_k Bm REALLOC_STACK regs1 a /\
              ~ (bv_unsigned out1 <= a < bv_unsigned out1 + bv_unsigned cap1)).
  { destruct HA as [HA|HA].
    - split; [left; lia|].
      split; [intros Ho; pose proof (sb_low Bm API L1 A1 mem1 md1 a HM1 Ho); lia|].
      split; [intros Ho; pose proof (sb_low Bm API L2 A2 m2 md2 a M2 Ho); lia|].
      split; [unfold scratch_k; rewrite SPR; unfold REALLOC_STACK, ALLOC_STACK; intros [X|X]; lia|].
      intros X. destruct (HE2 a X). lia.
    - pose proof HA as (Hi & Hs & Hc & He). pose proof (in_img_low Bm H01 a Hi) as IL.
      split; [right; exact Hi|].
      split; [exact (sb_not_owned_img Bm API AX L1 A1 mem1 md1 a HM1 HA)|].
      split; [exact (sb_not_owned_img Bm API AX L2 A2 m2 md2 a M2 HA)|].
      split; [unfold scratch_k; rewrite SPR; unfold REALLOC_STACK, ALLOC_STACK; intros [X|X]; [lia | exact (He X)]|].
      intros X. destruct (HE2 a X) as [_ NI]. exact (NI Hi). }
  destruct K as (K1 & K2 & K3 & K4 & K5).
  rewrite <- H01. destruct (FR2 a K1 K2 K3 K4 K5) as [E1 E2]. split; [exact E1 | apply E2].
Qed.

Lemma sr_surv : forall L1 A1 mem1 md1 j cap1 out1 q kq,
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs mem1 md1 ->
  SBLK j L1 A1 cap1 out1 -> live = true ->
  In (q, kq) (blocks L A) -> q <> OUT -> 0 < kq ->
  exists p, In (p, kq) (user_blocks A) /\ In (p, kq) (user_blocks A1) /\ ptr_addr L p = q /\ ptr_addr L1 p = q /\
    q <> bv_unsigned out1.
Proof using All.
  intros L1 A1 mem1 md1 j cap1 out1 q kq RP1 BLK LIVE IN NQ Kp.
  pose proof IN as IN0.
  unfold blocks in IN. apply in_map_iff in IN as ([p k'] & E & Hp). cbn [fst snd] in E. injection E as Ep Ek. subst k'.
  destruct RP1 as (_ & _ & _ & _ & _ & AD1 & SV1 & _).
  assert (NF : ~ (live = true /\ ptr_addr L p = OUT)) by (intros [_ X]; apply NQ; rewrite <- Ep; exact X).
  pose proof (SV1 p kq Hp Kp NF) as Hp1.
  pose proof (AD1 p kq Hp Hp1 NF) as Ea.
  exists p. split; [exact Hp|]. split; [exact Hp1|]. split; [exact Ep|]. split; [rewrite Ea; exact Ep|].
  destruct BLK as [(_ & _ & _ & _ & ->)|(_ & _ & _ & _ & _ & _ & NEQ)]; [exact NQ|].
  exact (NEQ q kq IN0 NQ Kp).
Qed.

Lemma sr_comp : forall L1 A1 regs1 mem1 md1 j cap1 out1 L2 A2 R2 m2 md2,
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs mem1 md1 ->
  SBLK j L1 A1 cap1 out1 -> live = true -> spZ regs1 = SP - 112 ->
  relay_post Bm API REALLOC_STACK (fun x => bv_unsigned out1 <= x < bv_unsigned out1 + bv_unsigned cap1)
    (fun q => q = bv_unsigned out1) L1 A1 regs1 mem1 md1 L2 A2 R2 m2 md2 ->
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L2 A2 regs m2 md2.
Proof using All.
  intros L1 A1 regs1 mem1 md1 j cap1 out1 L2 A2 R2 m2 md2 RP1 BLK LIVE SPR RP2.
  pose proof (XA sb_tp) as (TP1 & TP2 & TP3). pose proof (XA sb_sp) as (S1 & S2 & S3 & S4).
  pose proof (zr_word out1) as Ro1. pose proof (zr_word cap1) as Rc1. unfold inr64 in *.
  pose proof (XA sb_blk_cases j L1 A1 cap1 out1 BLK) as BC.
  pose proof RP1 as (M1 & _).
  assert (HE2 : forall x, bv_unsigned out1 <= x < bv_unsigned out1 + bv_unsigned cap1 ->
                  x < YM05.alloc_ceiling /\ ~ in_img Bm x).
  { intros x Hx. destruct BC as [(Z0 & _)|(Cp & _ & (F1 & F2 & FI) & _)]; [lia|].
    split; [lia|]. replace x with (bv_unsigned out1 + (x - bv_unsigned out1)) by lia. apply FI. lia. }
  assert (SPE : spZ regs = SP) by reflexivity.
  eapply (sb_comp Bm API).
  all: try first [exact AX | exact CTXO | exact EU | exact BW | exact H01 | exact RP1 | exact RP2].
  - intros a Ha. rewrite SPE in Ha. unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in Ha. lia.
  - intros a [X|X]; [left|right; exact X]. rewrite SPE. rewrite SPR in X.
    unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in *. lia.
  - intros a [X|X] _ Y; cbv beta in Y; destruct (HE2 a Y) as [Y1 Y2].
    + rewrite SPE in X. unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in X. lia.
    + apply Y2. apply H14. exact X.
  - intros p n Hp _ Hn NF E. cbv beta in E.
    assert (NQ : ptr_addr L p <> OUT) by (intros X; apply NF; split; [exact LIVE | exact X]).
    assert (INq : In (ptr_addr L p, n) (blocks L A))
      by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hp]).
    destruct (sr_surv L1 A1 mem1 md1 j cap1 out1 (ptr_addr L p) n RP1 BLK LIVE INq NQ Hn) as (p' & _ & _ & _ & _ & NE).
    exact (NE E).
  - intros a Ha _ _ Y. cbv beta in Y. exfalso. destruct (HE2 a Y) as [Y1 Y2].
    destruct Ha as [Ha|Ha]; [lia | exact (Y2 Ha)].
  - intros p n i Hp Hp1 NF Hi Y. cbv beta in Y.
    assert (NQ : ptr_addr L p <> OUT) by (intros X; apply NF; split; [exact LIVE | exact X]).
    destruct BC as [(Z0 & _)|(Cp & _ & _ & IN1)]; [lia|].
    pose proof BLK as BLK0.
    destruct BLK as [(J0 & -> & -> & -> & ->)|(Jp & _)].
    + unfold send_writes. right. right. right. split; [exact LIVE | exact Y].
    + exfalso.
      assert (INq : In (ptr_addr L p, n) (blocks L A))
        by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hp]).
      destruct (sr_surv L1 A1 mem1 md1 j cap1 out1 (ptr_addr L p) n RP1 BLK0 LIVE INq NQ ltac:(lia))
        as (p' & _ & Hp1' & _ & Ea & NE).
      assert (INq1 : In (ptr_addr L p, n) (blocks L1 A1))
        by (unfold blocks; apply in_map_iff; exists (p', n); split; [cbn [fst snd]; rewrite Ea; reflexivity | exact Hp1']).
      destruct (blocks_disjoint Bm API L1 A1 mem1 md1 _ _ _ _ M1 INq1 IN1 NE); lia.
Qed.

Lemma sr_line : forall L1 A1 regs1 mem1 md1 j cap1 out1 L2 A2 R2 m2 md2 res n2 b1 b2 c1 c2,
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs mem1 md1 ->
  SBLK j L1 A1 cap1 out1 -> live = true -> spZ regs1 = SP - 112 ->
  relay_post Bm API REALLOC_STACK (fun x => bv_unsigned out1 <= x < bv_unsigned out1 + bv_unsigned cap1)
    (fun q => q = bv_unsigned out1) L1 A1 regs1 mem1 md1 L2 A2 R2 m2 md2 ->
  blocks L2 A2 = c1 ++ (res, n2) :: c2 -> c1 ++ c2 = b1 ++ b2 ->
  ((bv_unsigned cap1 = 0 /\ blocks L1 A1 = b1 ++ b2) \/
   (0 < bv_unsigned cap1 /\ blocks L1 A1 = b1 ++ (bv_unsigned out1, bv_unsigned cap1) :: b2)) ->
  fresh_block Bm res n2 -> 0 < n2 ->
  (forall i, 0 <= i < LEN -> mbyte rsegs m2 (LINE + i) = mbyte rsegs mem1 (LINE + i)) /\
  (LINE + LEN <= res \/ res + n2 <= LINE).
Proof using All.
  intros L1 A1 regs1 mem1 md1 j cap1 out1 L2 A2 R2 m2 md2 res n2 b1 b2 c1 c2 RP1 BLK LIVE SPR RP2 EB2 EC EB1 FR Npos.
  assert (NOFF : off = false).
  { unfold send_live in LIVE. apply andb_prop in LIVE as [N _]. apply negb_true_iff in N. exact N. }
  pose proof (XA sb_lenpos NOFF) as LPOS.
  pose proof (XA sb_blk_cases j L1 A1 cap1 out1 BLK) as BC.
  pose proof (zr_word (getr regs 10)) as Rl. pose proof (zr_word (getr regs 11)) as Rn.
  pose proof (zr_word out1) as Ro1. pose proof (zr_word cap1) as Rc1. unfold inr64 in *.
  pose proof FR as (F1 & F2 & F3).
  pose proof RP1 as (M1 & _).
  pose proof RP2 as (M2 & _ & _ & _ & _ & AD2 & SV2 & _ & _ & _ & _ & _ & BY2 & _).
  assert (HE2 : forall x, bv_unsigned out1 <= x < bv_unsigned out1 + bv_unsigned cap1 ->
                  x < YM05.alloc_ceiling /\ ~ in_img Bm x).
  { intros x Hx. destruct BC as [(Z0 & _)|(Cp & _ & (G1 & G2 & FI) & _)]; [lia|].
    split; [lia|]. replace x with (bv_unsigned out1 + (x - bv_unsigned out1)) by lia. apply FI. lia. }
  destruct H15 as [IMG|(q & kq & INq & Q1 & Q2 & NQ)].
  - split.
    + intros i Hi.
      refine (proj1 (sr_keep L1 A1 regs1 mem1 md1 L2 A2 R2 m2 md2 out1 cap1 (LINE + i) M1 RP2 SPR HE2
                      (or_intror (IMG (LINE + i) _)))). lia.
    + assert (P : forall i, 0 <= i < LEN -> in_img Bm (LINE + i))
        by (intros i Hi; refine (proj1 (IMG (LINE + i) _)); lia).
      destruct (sb_apart (in_img Bm) res n2 LINE LEN Npos LPOS F3 P); lia.
  - assert (Kp : 0 < kq) by lia.
    destruct (sr_surv L1 A1 mem1 md1 j cap1 out1 q kq RP1 BLK LIVE INq NQ Kp) as (p & Hp & Hp1 & Ep & Ep1 & NE).
    assert (NF2 : ~ (fun q0 => q0 = bv_unsigned out1) (ptr_addr L1 p)) by (cbv beta; rewrite Ep1; exact NE).
    pose proof (SV2 p kq Hp1 Kp NF2) as Hp2.
    assert (INq1 : In (q, kq) (blocks L1 A1))
      by (unfold blocks; apply in_map_iff; exists (p, kq); split; [cbn [fst snd]; rewrite Ep1; reflexivity | exact Hp1]).
    assert (DJ : bv_unsigned cap1 = 0 \/ q + kq <= bv_unsigned out1 \/ bv_unsigned out1 + bv_unsigned cap1 <= q).
    { destruct BC as [(Z0 & _)|(Cp & _ & _ & IN1)]; [left; exact Z0|right].
      destruct (blocks_disjoint Bm API L1 A1 mem1 md1 _ _ _ _ M1 INq1 IN1 NE) as [X|X]; [left|right]; lia. }
    split.
    + intros i Hi. replace (LINE + i) with (ptr_addr L1 p + (LINE + i - q)) by lia.
      rewrite <- H01. apply (BY2 p kq (LINE + i - q) Hp1 Hp2 NF2); [lia|]. cbv beta. lia.
    + assert (INq2 : In (q, kq) (b1 ++ b2)).
      { destruct EB1 as [(_ & E1)|(_ & E1)]; rewrite E1 in INq1; [exact INq1|].
        apply (sr_in_mid _ _ _ _ INq1). intros X. injection X as X1 X2. exact (NE X1). }
      rewrite <- EC in INq2.
      destruct (blocks_mid_disjoint Bm (aa_MR API) (aa_laws API) L2 A2 m2 md2 c1 c2 res n2 q kq M2 EB2 INq2); lia.
Qed.

Lemma sr_blk_next : forall L1 A1 mem1 md1 j cap1 out1 b1 b2 c1 c2,
  aa_MR API L1 A1 mem1 md1 -> SBLK j L1 A1 cap1 out1 -> c1 ++ c2 = b1 ++ b2 ->
  ((bv_unsigned cap1 = 0 /\ blocks L1 A1 = b1 ++ b2) \/
   (0 < bv_unsigned cap1 /\ blocks L1 A1 = b1 ++ (bv_unsigned out1, bv_unsigned cap1) :: b2)) ->
  exists b1' b2', c1 ++ c2 = b1' ++ b2' /\
    ((CAP = 0 /\ blocks L A = b1' ++ b2') \/ (0 < CAP /\ blocks L A = b1' ++ (OUT, CAP) :: b2')).
Proof using All.
  intros L1 A1 mem1 md1 j cap1 out1 b1 b2 c1 c2 HM BLK EC EB.
  destruct BLK as [(J0 & -> & -> & -> & ->)|(Jp & Cp & _ & _ & _ & (d1 & d2 & e1 & e2 & E1 & E2 & E3) & _)].
  - exists b1, b2. split; [exact EC|]. destruct EB as [(Z0 & E)|(Cp & E)]; [left|right]; split; assumption.
  - destruct EB as [(Z0 & _)|(_ & E)]; [lia|].
    assert (NI : forall l1 l2, blocks L1 A1 = l1 ++ (bv_unsigned out1, bv_unsigned cap1) :: l2 ->
                   ~ In (bv_unsigned out1, bv_unsigned cap1) l1).
    { intros l1 l2 El X.
      destruct (blocks_mid_disjoint Bm (aa_MR API) (aa_laws API) L1 A1 mem1 md1 l1 l2 _ _ _ _ HM El
                  (in_or_app _ _ _ (or_introl X))); lia. }
    pose proof E as E'. rewrite E1 in E.
    destruct (sr_mid_eq e1 e2 b1 b2 _ E (NI e1 e2 E1) (NI b1 b2 E')) as [-> ->].
    exists d1, d2. split; [rewrite EC; exact E2 | exact E3].
Qed.

Lemma sr_after : forall L1 A1 regs1 mem1 md1 j b p k nk1 cap1 out1 junk1 jb c1 n2 c2,
  n2 = 2 * (bv_unsigned nk1 + c1) ->
  SCREGS regs1 k nk1 out1 c1 -> ro_agree rsegs mem1 ->
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs mem1 md1 ->
  SBLK j L1 A1 cap1 out1 ->
  (forall L2 A2 q res, live_at L2 A2 q res n2 ->
     rt_ok RF A2 (if bv_unsigned cap1 =? 0 then rt_malloc RF b n2 else rt_realloc RF b (bv_unsigned cap1) n2 p q) ->
     SRES L2 A2 res k n2) ->
  st_init_done A1 = true ->
  off = false -> dd = 0 ->
  0 <= k < LEN -> bv_unsigned nk1 = NO + k -> NO + k <= bv_unsigned cap1 ->
  1 <= c1 <= LEN - k -> bv_unsigned cap1 < bv_unsigned nk1 + c1 ->
  c1 = (if bv_unsigned mx =? 0 then LEN - k else Z.min (LEN - k) (bv_unsigned mx)) ->
  rw_cells rsegs mem1 G_CLIENT [C4 (Z_to_bv 64 3)] ->
  rw_cells rsegs mem1 G_BROKEN [C1 (Z_to_bv 8 0)] -> rw_cells rsegs mem1 G_DEAD [C1 (Z_to_bv 8 0)] ->
  rw_cells rsegs mem1 G_EINTR [C1 (Z_to_bv 8 0)] ->
  rw_cells rsegs mem1 G_OUTV [C8 mx; C8 nk1; C8 cap1; C8 out1] ->
  bytes_at rsegs mem1 LINE Bl ->
  rw_cells rsegs mem1 (SP + -112) [CB 8 jb; C8 (reg_get regs 27); C8 (reg_get regs 26); C8 (reg_get regs 25);
     C8 (reg_get regs 24); C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
     C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  sr_rl b p cap1 out1 n2 (O ++ firstn (Z.to_nat k) Bl ++ junk1) L1 A1 regs1 mem1 md1 c2 ->
  (forall w' c', bv_unsigned cap1 < w' -> SCALL w' c' -> SR rsegs c' SPOST) ->
  SR rsegs c2 SPOST.
Proof using All.
  intros L1 A1 regs1 mem1 md1 j b pb k nk1 cap1 out1 junk1 jb c1 n2 c2 En2 CR RO1 RP1 BLK RESN INI1 NOFF D0 Hk Hnk Hck
    Hc1 Hcap Hcd CCL CBR CDD CEI COV BL FRM RL IHc.
  pose proof (XA sb_tp) as (TP1 & TP2 & TP3). pose proof (XA sb_sp) as (S1 & S2 & S3 & S4).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof H27 as MGR.
  pose proof (XA sb_lenpos NOFF) as LPOS. pose proof (XA sb_lo) as LO.
  pose proof (zr_word cap1) as Rc1. pose proof (zr_word out1) as Ro1. pose proof (zr_word nk1) as Rn1.
  pose proof (zr_word (getr regs 10)) as Rl. pose proof (zr_word (getr regs 11)) as Rln.
  pose proof (zr_word nout) as Rno. unfold inr64 in *.
  assert (HLG : SrOr (LINE + LEN <= 202912) (203000 <= LINE)) by exact H09.
  assert (HLE : SrOr (LINE + LEN <= bv_unsigned (getr regs 4) + -164) (bv_unsigned (getr regs 4) + -164 + 4 <= LINE))
    by (unfold SrOr; destruct H10; [left|right]; lc).
  assert (LIVE : live = true) by (unfold send_live; rewrite NOFF; cbn [negb andb]; apply Z.eqb_eq; exact D0).
  assert (CL3 : cl = 3)
    by (destruct H16 as [C3|C3]; [exact C3|]; unfold send_off in NOFF; rewrite C3 in NOFF; discriminate).
  pose proof CR as (E1_1 & E1_2 & E1_3 & E1_4 & E1_8 & E1_9 & E1_10 & E1_11 & E1_18 & E1_19 & E1_20 & E1_21 & E1_22 &
    E1_23 & E1_24 & E1_25 & E1_26 & E1_27).
  assert (SPR : spZ regs1 = SP - 112).
  { unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 (SP + -112))); [f_equal; exact E1_2|]. apply unsigned_lit. lia. }
  destruct RL as (L2 & A2 & R2 & m2 & md2 & res & -> & RP2 & A0 & NZ & FRESH & BLKS & RO2 & CPY & INI2 & q2 & LV2
    & RES2).
  pose proof FRESH as (F1 & F2 & F3).
  pose proof RP1 as (M1 & _).
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & PR2 & _ & _ & _ & SC2).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M2) as (Hh2 & Hl2 & _).
  pose proof (XA sb_blk_cases j L1 A1 cap1 out1 BLK) as BC.
  assert (HE2 : forall x, bv_unsigned out1 <= x < bv_unsigned out1 + bv_unsigned cap1 ->
                  x < YM05.alloc_ceiling /\ ~ in_img Bm x).
  { intros x Hx. destruct BC as [(Z0 & _)|(Cp & _ & (G1 & G2 & FI) & _)]; [lia|].
    split; [lia|]. replace x with (bv_unsigned out1 + (x - bv_unsigned out1)) by lia. apply FI. lia. }
  clear BC.
  assert (URES : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (UN2 : bv_unsigned (Z_to_bv 64 n2) = n2) by (apply unsigned_lit; lia).
  (* frame of the realloc call *)
  assert (TG : forall a cs, rw_cells rsegs mem1 a cs ->
             (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_plain Bm (a + i)) -> rw_cells rsegs m2 a cs).
  { intros a cs H P. apply (rw_cells_transfer rsegs mem1 m2 a cs H). intros i Hi.
    exact (sr_keep L1 A1 regs1 mem1 md1 L2 A2 R2 m2 md2 out1 cap1 (a + i) M1 RP2 SPR HE2 (or_intror (P i Hi))). }
  assert (CCL2 : rw_cells rsegs m2 G_CLIENT [C4 (Z_to_bv 64 3)])
    by (apply TG; [exact CCL | intros i Hi; cbn in Hi; apply H13; lia]).
  assert (CBR2 : rw_cells rsegs m2 G_BROKEN [C1 (Z_to_bv 8 0)])
    by (apply TG; [exact CBR | intros i Hi; cbn in Hi; apply H12; unfold G_RELAY_LO, G_RELAY_HI, G_BROKEN; lia]).
  assert (CDD2 : rw_cells rsegs m2 G_DEAD [C1 (Z_to_bv 8 0)])
    by (apply TG; [exact CDD | intros i Hi; cbn in Hi; apply H12; unfold G_RELAY_LO, G_RELAY_HI, G_DEAD; lia]).
  assert (CEI2 : rw_cells rsegs m2 G_EINTR [C1 (Z_to_bv 8 0)])
    by (apply TG; [exact CEI | intros i Hi; cbn in Hi; apply H12; unfold G_RELAY_LO, G_RELAY_HI, G_EINTR; lia]).
  assert (COV2 : rw_cells rsegs m2 G_OUTV [C8 mx; C8 nk1; C8 cap1; C8 out1])
    by (apply TG; [exact COV | intros i Hi; cbn in Hi; apply H12; unfold G_RELAY_LO, G_RELAY_HI, G_OUTV; lia]).
  assert (FRM2 : rw_cells rsegs m2 (SP + -112) [CB 8 jb; C8 (reg_get regs 27); C8 (reg_get regs 26);
     C8 (reg_get regs 25); C8 (reg_get regs 24); C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21);
     C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
     C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs mem1 m2 _ _ FRM). intros i Hi. cbn in Hi.
    refine (sr_keep L1 A1 regs1 mem1 md1 L2 A2 R2 m2 md2 out1 cap1 (SP + -112 + i) M1 RP2 SPR HE2
             (or_introl _)). lia. }
  assert (ST2 : stk rsegs m2 (SP - 8368) (SP + -112)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs m2 a).
    { rewrite <- H01. apply SC2. left. rewrite SPR. unfold REALLOC_STACK, ALLOC_STACK. lia. }
    split; [exact W|]. destruct (writable_hi_present m2 a ltac:(lia) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  destruct (sb_c4 m2 ERR ltac:(lia) ltac:(lia) ltac:(intros i Hi; rewrite <- H01; apply SC2; right; lia))
    as [ev2 CER2].
  (* the line, and the new block apart from it and from the globals *)
  destruct BLKS as (b1 & b2 & cc1 & cc2 & EB2 & EC & EB1).
  assert (N2pos : 0 < n2) by lia.
  destruct (sr_line L1 A1 regs1 mem1 md1 j cap1 out1 L2 A2 R2 m2 md2 res n2 b1 b2 cc1 cc2
              RP1 BLK LIVE SPR RP2 EB2 EC EB1 FRESH N2pos) as (LK & LA0).
  assert (LA : SrOr (LINE + LEN <= res) (res + n2 <= LINE)) by exact LA0. clear LA0.
  assert (BL2 : bytes_at rsegs m2 LINE Bl).
  { apply (bytes_at_transfer rsegs mem1); [exact BL|]. intros i Hi. rewrite H08 in Hi. exact (LK i Hi). }
  assert (DA1 : SrOr (res + n2 <= 202912) (203000 <= res)).
  { assert (P : forall i, 0 <= i < 88 -> in_img Bm (202912 + i))
      by (intros i Hi; refine (proj1 (H12 (202912 + i) _)); unfold G_RELAY_LO, G_RELAY_HI; lia).
    unfold SrOr. destruct (sb_apart (in_img Bm) res n2 202912 88 N2pos ltac:(lia) F3 P); lc. }
  assert (DA2 : SrOr (res + n2 <= 136740) (136744 <= res)).
  { assert (P : forall i, 0 <= i < 4 -> in_img Bm (136740 + i))
      by (intros i Hi; refine (proj1 (H13 (136740 + i) _)); unfold G_CLIENT; lia).
    unfold SrOr. destruct (sb_apart (in_img Bm) res n2 136740 4 N2pos ltac:(lia) F3 P); lc. }
  assert (DA3 : SrOr (res + n2 <= ERR) (ERR + 4 <= res)).
  { assert (P : forall i, 0 <= i < 4 -> in_img Bm (ERR + i)) by (intros i Hi; apply H14; lia).
    unfold SrOr. destruct (sb_apart (in_img Bm) res n2 ERR 4 N2pos ltac:(lia) F3 P); lc. }
  (* the grown block: the kept prefix of the line, then junk *)
  assert (INB : In (res, n2) (blocks L2 A2)) by (rewrite EB2; apply in_or_app; right; left; reflexivity).
  assert (PRS : forall i, 0 <= i < n2 -> present m2 (res + i))
    by (intros i Hi; exact (proj1 (block_facts Bm (aa_MR API) (aa_laws API) L2 A2 m2 md2 _ _ i M2 INB Hi))).
  apply bytes_at_app in CPY. destruct CPY as [OB2 CPY]. apply bytes_at_app in CPY. destruct CPY as [KB2 _].
  rewrite LO in KB2.
  assert (LFK : length (firstn (Z.to_nat k) Bl) = Z.to_nat k) by (apply firstn_length_le; lia).
  assert (CB1 : rw_cells rsegs m2 (res + NO) [CB (Z.to_nat k) (firstn (Z.to_nat k) Bl)]).
  { pose proof (sr_cb m2 (res + NO) _ KB2) as X. rewrite LFK in X. apply X.
    intros i Hi. replace (res + NO + i) with (res + (NO + i)) by lia. apply PRS. lia. }
  destruct (present_rw_cells rsegs m2 (res + NO + k) (Z.to_nat (n2 - bv_unsigned nk1)) ltac:(lia) ltac:(lia)
              ltac:(intros i Hi; replace (res + NO + k + i) with (res + (NO + k + i)) by lia; apply PRS; lia))
    as [junk2 CB2].
  assert (CO2 : rw_cells rsegs m2 (res + NO)
                  [CB (Z.to_nat k) (firstn (Z.to_nat k) Bl); CB (Z.to_nat (n2 - bv_unsigned nk1)) junk2]).
  { apply (sl_cells_app_r rsegs m2 (res + NO) [_] [_] CB1).
    match goal with |- rw_cells _ _ ?X _ => replace X with (res + NO + k) by (cbn [cells_size csize]; lia) end.
    exact CB2. }
  (* the new block in the frame of send_line *)
  assert (BLK2 : SBLK (S j) L2 A2 (Z_to_bv 64 n2) (Z_to_bv 64 res)).
  { right. rewrite URES, UN2.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact FRESH|].
    split.
    { destruct (sr_blk_next L1 A1 mem1 md1 j cap1 out1 b1 b2 cc1 cc2 M1 BLK EC EB1) as (b1' & b2' & X1 & X2).
      exists b1', b2', cc1, cc2. split; [exact EB2|]. split; [exact X1 | exact X2]. }
    intros q m Hq Hne Hm.
      destruct (sr_surv L1 A1 mem1 md1 j cap1 out1 q m RP1 BLK LIVE Hq Hne Hm) as (p & _ & Hp1 & _ & Ep1 & NE).
      assert (INq : In (q, m) (cc1 ++ cc2)).
      { rewrite EC.
        assert (X : In (q, m) (blocks L1 A1))
          by (unfold blocks; apply in_map_iff; exists (p, m); split; [cbn [fst snd]; rewrite Ep1; reflexivity | exact Hp1]).
        destruct EB1 as [(_ & E)|(_ & E)]; rewrite E in X; [exact X|].
        apply (sr_in_mid _ _ _ _ X). intros Y. injection Y as Y1 Y2. exact (NE Y1). }
      destruct (blocks_mid_disjoint Bm (aa_MR API) (aa_laws API) L2 A2 m2 md2 cc1 cc2 res n2 q m M2 EB2 INq); lia. }
  clear EB1.
  pose proof (sr_comp L1 A1 regs1 mem1 md1 j cap1 out1 L2 A2 R2 m2 md2 RP1 BLK LIVE SPR RP2) as RPc.
  (* normalized memory for the Kind A run *)
  pose proof (mem_inv_normalize rsegs m2) as MI2n.
  assert (ROO : forall x, res <= x < res + n2 -> ro_addr rsegs (wa x) = false).
  { intros x Hx. apply (ro_addr_out Bm H01); [lia|]. replace x with (res + (x - res)) by lia. apply F3. lia. }
  pose proof (sb_nrw m2 _ _ RO2 CCL2 ltac:(unfold G_CLIENT; lia)) as CCLn.
  pose proof (sb_nrw m2 _ _ RO2 CBR2 ltac:(unfold G_BROKEN; lia)) as CBRn.
  pose proof (sb_nrw m2 _ _ RO2 CDD2 ltac:(unfold G_DEAD; lia)) as CDDn.
  pose proof (sb_nrw m2 _ _ RO2 CEI2 ltac:(unfold G_EINTR; lia)) as CEIn.
  pose proof (sb_nrw m2 _ _ RO2 COV2 ltac:(unfold G_OUTV; lia)) as COVn.
  pose proof (sb_nrw m2 _ _ RO2 CER2 ltac:(lia)) as CERn.
  pose proof (sb_nrw m2 _ _ RO2 FRM2 ltac:(lia)) as FRMn.
  pose proof (stk_normalize m2 _ _ ST2 ltac:(lia)) as STn.
  pose proof (bytes_at_normalize rsegs m2 _ _ RO2 BL2) as BLn.
  pose proof (sb_rw_norm m2 _ _ RO2 CO2 ltac:(intros i Hi; apply ROO; cbn in Hi; lia)) as COn.
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (SP + -112))
    by exact (eq_trans (PR2 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_3 : reg_get R2 3 = getr regs 3) by exact (eq_trans (PR2 3 ltac:(unfold callee_saved; lia)) E1_3).
  assert (E2_4 : reg_get R2 4 = getr regs 4) by exact (eq_trans (PR2 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (E2_8 : reg_get R2 8 = getr regs 11) by exact (eq_trans (PR2 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (E2_9 : reg_get R2 9 = getr regs 10) by exact (eq_trans (PR2 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 res) by exact A0.
  assert (E2_18 : reg_get R2 18 = Z_to_bv 64 (k + LINE))
    by exact (eq_trans (PR2 18 ltac:(unfold callee_saved; lia)) E1_18).
  assert (E2_19 : reg_get R2 19 = Z_to_bv 64 c1)
    by exact (eq_trans (PR2 19 ltac:(unfold callee_saved; lia)) E1_19).
  assert (E2_20 : reg_get R2 20 = Z_to_bv 64 (2 * (bv_unsigned nk1 + c1)))
    by exact (eq_trans (PR2 20 ltac:(unfold callee_saved; lia)) E1_20).
  assert (E2_21 : reg_get R2 21 = Z_to_bv 64 136040)
    by exact (eq_trans (PR2 21 ltac:(unfold callee_saved; lia)) E1_21).
  assert (E2_22 : reg_get R2 22 = Z_to_bv 64 202912)
    by exact (eq_trans (PR2 22 ltac:(unfold callee_saved; lia)) E1_22).
  assert (E2_23 : reg_get R2 23 = Z_to_bv 64 k)
    by exact (eq_trans (PR2 23 ltac:(unfold callee_saved; lia)) E1_23).
  assert (E2_24 : reg_get R2 24 = Z_to_bv 64 1)
    by exact (eq_trans (PR2 24 ltac:(unfold callee_saved; lia)) E1_24).
  assert (E2_25 : reg_get R2 25 = Z_to_bv 64 3)
    by exact (eq_trans (PR2 25 ltac:(unfold callee_saved; lia)) E1_25).
  assert (E2_26 : reg_get R2 26 = Z_to_bv 64 4)
    by exact (eq_trans (PR2 26 ltac:(unfold callee_saved; lia)) E1_26).
  assert (E2_27 : reg_get R2 27 = nk1)
    by exact (eq_trans (PR2 27 ltac:(unfold callee_saved; lia)) E1_27).
  subst n2.
  replace (getr regs1 1) with (Z_to_bv 64 0x13454) by (symmetry; exact E1_1).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2_2, E2_3, E2_4, E2_8, E2_9, E2_10, E2_18, E2_19, E2_20, E2_21, E2_22, E2_23, E2_24, E2_25, E2_26, E2_27.
    eapply (evt_normalize rsegs); [exact sb_wx | exact RO2 |].
    eapply sl_back with (lo := SP - 8368) (B := Bl) (jb := jb) (k := k) (ev := ev2) (nk := nk1) (c := c1)
      (r := 2 * (bv_unsigned nk1 + c1) - bv_unsigned nk1) (junk := junk2) (res := Z_to_bv 64 res)
      (m1 := normalize rsegs m2).
    all: try first [exact MC | exact EL | exact H08 | exact CCLn | exact COVn | exact HLG | exact HLE | exact Hcd
                   | exact sr_hem | exact sr_hl0 | lc].
    all: try (unfold sl_frame; split; [exact FRMn | exact STn]).
    unfold sl_pre. rewrite URES, UN2.
    split; [lc|]. split; [lc|]. split; [lc|]. split; [lc|].
    split; [exact MI2n|]. split; [exact BLn|].
    split; [exact CBRn|]. split; [exact CDDn|]. split; [exact CEIn|].
    split; [replace (bv_unsigned (getr regs 4) + -164) with ERR by lc; exact CERn|].
    split; [lc|].
    split; [split; [destruct DA1 as [X|X]; [left|right]; lc | destruct DA2 as [X|X]; [left|right]; lc]|].
    split; [destruct DA3 as [X|X]; [left|right]; lc|].
    split; [destruct LA as [X|X]; [left|right]; lc|].
    replace (res + bv_unsigned nk1 - k) with (res + NO) by lc. exact COn. }
  intros ms3 (can3 & (s3 & HQ & REL & ROS) & EQ).
  destruct HQ as (m1' & MU1 & WM1 & _ & [FIN|CALL]).
  - apply SR_ret.
    apply (XA sb_fin L2 A2 m2 md2 (S j) (Z_to_bv 64 (2 * (bv_unsigned nk1 + c1))) (Z_to_bv 64 res)
             [(202984, 203000)] 0 k ev2 nk1 (2 * (bv_unsigned nk1 + c1) - bv_unsigned nk1) m1' ms3 can3 s3).
    + exact RO2.
    + exact RPc.
    + exact BLK2.
    + intros _. rewrite URES, UN2. exact (RESN L2 A2 q2 res LV2 RES2).
    + exact INI2.
    + exact NOFF.
    + intros LF. rewrite LIVE in LF. discriminate.
    + intros _. rewrite URES, UN2. split; [exact OB2|]. lia.
    + rewrite CL3. exact CCL2.
    + intros lo hi [E|[]]. injection E as <- <-. right. lia.
    + exact MU1.
    + exact WM1.
    + rewrite D0. exact FIN.
    + exact REL.
    + exact ROS.
    + exact EQ.
  - apply (IHc (bv_unsigned (Z_to_bv 64 (2 * (bv_unsigned nk1 + c1))))); [rewrite UN2; lia|].
    apply (XA sb_next L2 A2 m2 md2 (S j) (Z_to_bv 64 (2 * (bv_unsigned nk1 + c1))) (Z_to_bv 64 res)
             [(202984, 203000)] jb 0 k ev2 nk1 (2 * (bv_unsigned nk1 + c1) - bv_unsigned nk1) m1' ms3 can3 s3).
    + exact RO2.
    + exact RPc.
    + exact BLK2.
    + intros _. rewrite URES, UN2. exact (RESN L2 A2 q2 res LV2 RES2).
    + exact INI2.
    + exact NOFF.
    + intros _. rewrite URES, UN2. split; [exact OB2|]. lia.
    + rewrite CL3. exact CCL2.
    + intros lo hi [E|[]]. injection E as <- <-. right. lia.
    + exact MU1.
    + exact WM1.
    + rewrite D0. exact CALL.
    + exact REL.
    + exact ROS.
    + exact EQ.
Qed.

Lemma sr_loop : forall (n : nat) w c, (Z.to_nat (2 * (NO + LEN) - w) < n)%nat -> SCALL w c -> SR rsegs c SPOST.
Proof using All.
  induction n as [|n IH]; intros w c Hn CALL; [lia|].
  unfold sb_call in CALL.
  destruct CALL as (L1 & A1 & regs1 & mem1 & md1 & j & k & nk1 & cap1 & out1 & junk1 & jb & c1 & -> & -> & CR & RO1
    & RP1 & BLK & RES1 & INI1 & NOFF & D0 & Hk & Hnk & Hck & Hc1 & Hcap & Hcd & CCL & CBR & CDD & CEI & COV & BL & OB
    & CO & FRM).
  rewrite H01.
  pose proof (XA sb_lo) as LO.
  pose proof (zr_word cap1) as Rc1. pose proof (zr_word nk1) as Rn1. unfold inr64 in *.
  pose proof (sr_pre L1 A1 regs1 mem1 md1 k nk1 out1 c1 RP1 INI1 CR) as PRE.
  pose proof CR as (E1_1 & _ & _ & _ & _ & _ & E1_10 & E1_11 & _).
  pose proof (zr_word mx) as Rmx. unfold inr64 in Rmx.
  destruct RES1 as (tp & qp & jr & o & LQ & NR & WFt & OKo & RT1 & RT3 & RT4 & RT5 & LV1).
  (* this round grows the buffer: the head request of the rest of the trace *)
  assert (G : sl_rest (bv_unsigned mx) LEN NO k (bv_unsigned cap1) jr o =
    ((if bv_unsigned cap1 =? 0 then RMalloc (2 * (bv_unsigned nk1 + c1))
      else RRealloc (bv_unsigned cap1) (2 * (bv_unsigned nk1 + c1)) o) ::
       fst (sl_rest (bv_unsigned mx) LEN NO (k + c1) (2 * (bv_unsigned nk1 + c1)) (S jr) (Ret jr)),
     snd (sl_rest (bv_unsigned mx) LEN NO (k + c1) (2 * (bv_unsigned nk1 + c1)) (S jr) (Ret jr)))).
  { rewrite Hnk. apply sl_rest_grow; [lc | lc | rewrite sl_n_eq; exact Hcd | lc]. }
  assert (ROOM : rt_room RF (runF RF qp bnd tp) (2 * (bv_unsigned nk1 + c1))).
  { rewrite G in RT3. cbn [fst] in RT3.
    refine (p3a_room_next RF qp bnd tp _ _ _ WFt ltac:(lia)
              (eq_ind_r (fun t => forall qs, length qs = nretF t -> roomF RF qs bnd t) H29 RT3) _).
    destruct (bv_unsigned cap1 =? 0); [left; reflexivity | right; do 2 eexists; reflexivity]. }
  assert (RESN : forall L2 A2 q res, live_at L2 A2 q res (2 * (bv_unsigned nk1 + c1)) ->
      rt_ok RF A2 (if bv_unsigned cap1 =? 0 then rt_malloc RF (runF RF qp bnd tp) (2 * (bv_unsigned nk1 + c1))
                   else rt_realloc RF (runF RF qp bnd tp) (bv_unsigned cap1) (2 * (bv_unsigned nk1 + c1))
                          (resolveF qp o) q) ->
      SRES L2 A2 res k (2 * (bv_unsigned nk1 + c1))).
  { intros L2 A2 q res LV2 R2. unfold sb_res.
    rewrite G in RT3, RT4, RT5. cbn [fst snd] in RT3, RT4, RT5.
    exists (tp ++ [if bv_unsigned cap1 =? 0 then RMalloc (2 * (bv_unsigned nk1 + c1))
                   else RRealloc (bv_unsigned cap1) (2 * (bv_unsigned nk1 + c1)) o]), (qp ++ [q]), (S jr), (Ret jr).
    rewrite (sl_rest_fit (bv_unsigned mx) LEN NO k (2 * (bv_unsigned nk1 + c1)) (S jr) (Ret jr) c1)
      by first [rewrite sl_n_eq; exact Hcd | lc].
    split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite nret_app, NR; destruct (bv_unsigned cap1 =? 0); cbn; lia|].
    split.
    { apply p3a_wf_snoc; [exact WFt|]. destruct (bv_unsigned cap1 =? 0); [exact I|].
      rewrite NR. exact OKo. }
    split; [cbn; lia|].
    split.
    { revert R2. destruct (bv_unsigned cap1 =? 0); intros R2.
      - rewrite p3a_runF_mal by (exact WFt || lia). exact R2.
      - rewrite p3a_runF_rea by first [exact WFt | lia | (rewrite LQ; exact OKo)]. exact R2. }
    split; [rewrite <- app_assoc; exact RT3|].
    split; [exact RT4|]. split; [exact RT5|].
    intros _. cbn [resolve].
    rewrite p3a_nth_last by lia. exact LV2. }
  pose proof CO as [[WF BT] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (WF1 & WF2 & _).
  cbn [cells_bytes cbytes] in BT. rewrite app_nil_r in BT.
  assert (OLD : bytes_at rsegs mem1 (bv_unsigned out1) (O ++ firstn (Z.to_nat k) Bl ++ junk1)).
  { apply bytes_at_app. split; [exact OB|]. rewrite LO. exact BT. }
  assert (LOLD : Z.of_nat (length (O ++ firstn (Z.to_nat k) Bl ++ junk1)) = bv_unsigned cap1).
  { rewrite !length_app, WF1, WF2. lc. }
  apply (SR_bind _ _ (sr_rl (runF RF qp bnd tp) (resolveF qp o) cap1 out1 (2 * (bv_unsigned nk1 + c1))
                        (O ++ firstn (Z.to_nat k) Bl ++ junk1) L1 A1 regs1 mem1 md1)).
  { destruct (XA sb_blk_cases j L1 A1 cap1 out1 BLK) as [(Z0 & O0 & N0 & OE & J0 & EL1 & EA1)|(Cp & NOle & FRE & IN1)].
    - apply (sr_rl_rn L1 A1 regs1 mem1 md1 (runF RF qp bnd tp) (resolveF qp o) cap1 out1); [exact PRE | exact RO1
        | exact Z0 | exact O0
        | exact E1_10 | exact E1_11 | | lc
        | exact (ra_ne_malloc Bm regs1 0x13454 0x1608c E1_1 HMPC ltac:(vm_compute; reflexivity)) | exact RT1 | exact ROOM].
      apply length_zero_iff_nil. rewrite !length_app, WF1, WF2. lc.
    - apply (sr_rl_ra L1 A1 regs1 mem1 md1 (runF RF qp bnd tp) (resolveF qp o) cap1 out1); [exact PRE | exact RO1
        | exact Cp | exact (LV1 Cp)
        | exact E1_10 | exact E1_11 | lc | exact OLD | exact LOLD | exact RT1 | exact ROOM]. }
  intros c2 RL.
  apply (sr_after L1 A1 regs1 mem1 md1 j (runF RF qp bnd tp) (resolveF qp o) k nk1 cap1 out1 junk1 jb c1
           (2 * (bv_unsigned nk1 + c1)) c2
           eq_refl CR RO1 RP1 BLK RESN INI1 NOFF D0 Hk Hnk Hck Hc1 Hcap Hcd CCL CBR CDD CEI COV BL FRM RL).
  intros w' c' Hw' CALL'. apply (IH w' c'); [lc | exact CALL'].
Qed.

Lemma sr_off : forall (m1 : word -> option byte) (ms1 can1 : machine_state)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  off = true ->
  munch [(SP - 112, SP)] (normalize rsegs mem) m1 -> wmono rsegs (normalize rsegs mem) m1 ->
  ms_rel rsegs can1 (MS (mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2
      (reg_get regs 8) (reg_get regs 9) a0 a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
      (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
      (reg_get regs 27) t3 t4 t5 t6) fp_regs (ret_pc (reg_get regs 1)) fp_csr None m1 (seg_rom rsegs)) ->
  ro_same rsegs mem (ms_mem can1) -> Regs6ss.ms_eqv can1 ms1 ->
  SPOST (mkCfg ms1 md).
Proof using All.
  intros m1 ms1 can1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 OFF MU0 WM0 REL ROS EQ.
  pose proof (XA sb_tp) as (TP1 & TP2 & TP3). pose proof (XA sb_sp) as (S1 & S2 & S3 & S4).
  pose proof H02 as (HM & HWF & HBD & HRA & _).
  pose proof H06 as RO0. rewrite H01 in RO0.
  pose proof (zr_word (getr regs 10)) as Rl. pose proof (zr_word (getr regs 11)) as Rn. unfold inr64 in *.
  assert (HL : SrOr (LINE + LEN <= SP - 8368) (SP <= LINE)) by exact H11.
  assert (LF : live = false) by (unfold send_live; rewrite OFF; reflexivity).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [CAN HR].
  rewrite CAN in EQ.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R3 & -> & X3).
  remember (ms_mem can1) as m3 eqn:Em3. clear Em3 CAN.
  destruct (sb_back mem m1 m3 _ RO0 HR ROS MU0 WM0) as (MU3 & WM3 & RO3).
  pose proof (sb_pres regs R3 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 X3) as PRS.
  assert (SPE : spZ regs = SP) by reflexivity.
  assert (RPm : relay_post Bm API SEND_LINE_K EE FF L A regs mem md L A regs m3 md).
  { eapply (sb_kA Bm API AX EU BW H01); [exact (XA sb_rp_refl) | exact MU3 | rewrite H01; exact WM3 | exact H14 |].
    intros a Ha. destruct (sb_outside_dec [(SP - 112, SP)] a) as [Ho|(lo & hi & Hin & Hlh)]; [left; exact Ho|].
    right; left. destruct Hin as [E|[]]. injection E as <- <-. rewrite SPE.
    unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK. lc. }
  pose proof (sb_rp_regs Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RPm PRS) as RPf.
  pose proof (ret_pc_of_ok _ HRA) as RPC. rewrite sb_getr in RPC.
  change (reg_get regs 1) with (getr regs 1). rewrite RPC.
  assert (TR : forall a cs, rw_cells (ms_segs Bm) mem a cs -> a + Z.of_nat (cells_size cs) <= SP - 112 ->
             rw_cells (ms_segs Bm) m3 a cs).
  { intros a cs H Ha. rewrite H01 in H |- *. apply (rw_cells_transport rsegs _ mem m3 _ _ H MU3 WM3).
    cbn [disjoint_from]. split; [lc | exact I]. }
  exists L, A, R3, m3, md, 0, 0, (@nil byte).
  split; [rewrite H01; reflexivity|].
  split; [exact RPf|]. split; [exact H03|].
  split; [exists []; unfold send_line_tr; rewrite LF; split; [reflexivity | split; [exact H28 | intros LT; discriminate LT]]|].
  split; [rewrite H01; exact RO3|].
  split.
  { rewrite H01. pose proof H07 as BL0. rewrite H01 in BL0.
    apply (bytes_at_transport rsegs _ mem m3 _ _ BL0 MU3). cbn [disjoint_from].
    split; [destruct HL as [X|X]; [left|right]; lc | exact I]. }
  split; [apply TR; [exact H20 | cbn [cells_size csize Nat.add]; unfold G_CLIENT; lc]|].
  split; [rewrite OFF; apply TR; [exact H21 | cbn [cells_size csize Nat.add]; unfold G_BROKEN; lc]|].
  split; [apply TR; [exact H22 | cbn [cells_size csize Nat.add]; unfold G_DEAD; lc]|].
  split; [rewrite OFF; apply TR; [exact H23 | cbn [cells_size csize Nat.add]; unfold G_EINTR; lc]|].
  split.
  { intros _. split; [reflexivity|]. rewrite OFF.
    split; [apply TR; [exact H25 | cbn [cells_size csize Nat.add]; lc]
           | apply TR; [exact H24 | cbn [cells_size csize Nat.add]; unfold G_OUTV; lc]]. }
  intros LT. rewrite LF in LT. discriminate.
Qed.

Lemma sr_main : SR (ms_segs Bm) (mkCfg (YK11.mkst regs (Z_to_bv 64 SEND_LINE) mem (seg_rom (ms_segs Bm))) md) SPOST.
Proof using All.
  pose proof (XA sb_tp) as (TP1 & TP2 & TP3). pose proof (XA sb_sp) as (S1 & S2 & S3 & S4).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof H27 as MGR.
  pose proof H02 as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof (XA sb_lo) as LO.
  pose proof (zr_word (getr regs 10)) as Rl. pose proof (zr_word (getr regs 11)) as Rn.
  pose proof (zr_word nout) as Rno. pose proof (zr_word cap) as Rca. pose proof (zr_word out) as Rou.
  unfold inr64 in *.
  assert (SPE : spZ regs = SP) by reflexivity.
  assert (ER2 : bv_unsigned (reg_get regs 2) = SP) by reflexivity.
  assert (ER4 : bv_unsigned (reg_get regs 4) = bv_unsigned (getr regs 4)) by reflexivity.
  assert (ER10 : bv_unsigned (reg_get regs 10) = LINE) by reflexivity.
  assert (ER11 : bv_unsigned (reg_get regs 11) = LEN) by reflexivity.
  assert (HLG : SrOr (bv_unsigned (reg_get regs 10) + bv_unsigned (reg_get regs 11) <= 202912)
                     (203000 <= bv_unsigned (reg_get regs 10))) by exact H09.
  assert (HLE : SrOr (bv_unsigned (reg_get regs 10) + bv_unsigned (reg_get regs 11) <= bv_unsigned (reg_get regs 4) + -164)
                     (bv_unsigned (reg_get regs 4) + -164 + 4 <= bv_unsigned (reg_get regs 10)))
    by (unfold SrOr; destruct H10; [left|right]; lc).
  assert (HLF : SrOr (bv_unsigned (reg_get regs 10) + bv_unsigned (reg_get regs 11) <= bv_unsigned (reg_get regs 2) - 112)
                     (bv_unsigned (reg_get regs 2) <= bv_unsigned (reg_get regs 10))).
  { unfold SrOr. destruct H11 as [X|X]; unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in X;
      [left|right]; lc. }
  pose proof H06 as RO0. rewrite H01 in RO0.
  pose proof H07 as BL0. rewrite H01 in BL0.
  pose proof H20 as CCL. pose proof H21 as CBR. pose proof H22 as CDD. pose proof H23 as CEI.
  pose proof H24 as COV. pose proof H25 as CER.
  rewrite H01 in CCL, CBR, CDD, CEI, COV, CER.
  assert (OBC : bytes_at rsegs mem OUT O /\ NO <= CAP).
  { destruct H26 as [(C0 & O0 & N0 & OE)|(Cp & NOle & IN & FRE & OJ & _)].
    - rewrite OE. split; [|lc]. split; [lc|]. split; [cbn; lc|]. intros i Hi. cbn in Hi. lc.
    - rewrite H01 in OJ. apply bytes_at_app in OJ as [OJ _]. split; [exact OJ | lc]. }
  destruct OBC as [OB0 CN].
  assert (ST : stk rsegs mem (SP - 8368) SP).
  { split; [lc|]. split; [lc|]. intros a Ha.
    assert (W : writable_at rsegs mem a).
    { rewrite <- H01. apply HWS. rewrite SPE. unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK. lc. }
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lc) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (stk_normalize mem _ _ ST ltac:(lc)) as ST0.
  pose proof (mem_inv_normalize rsegs mem) as MI0.
  pose proof (bytes_at_normalize rsegs mem _ _ RO0 BL0) as BLn.
  pose proof (sb_nrw mem _ _ RO0 CCL ltac:(unfold G_CLIENT; lc)) as CCLn.
  pose proof (sb_nrw mem _ _ RO0 CBR ltac:(unfold G_BROKEN; lc)) as CBRn.
  pose proof (sb_nrw mem _ _ RO0 CDD ltac:(unfold G_DEAD; lc)) as CDDn.
  pose proof (sb_nrw mem _ _ RO0 CEI ltac:(unfold G_EINTR; lc)) as CEIn.
  pose proof (sb_nrw mem _ _ RO0 COV ltac:(unfold G_OUTV; lc)) as COVn.
  pose proof (sb_nrw mem _ _ RO0 CER ltac:(lc)) as CERn.
  assert (CERn' : rw_cells rsegs (normalize rsegs mem) (bv_unsigned (reg_get regs 4) + -164) [C4 ev])
    by (replace (bv_unsigned (reg_get regs 4) + -164) with ERR by lc; exact CERn).
  assert (RES0 : live = true -> SRES L A OUT 0 CAP).
  { intros LIVE. unfold sb_res. exists [], [], 0%nat, (known_at L A OUT).
    unfold send_line_tr, send_line_cap, send_line_out. rewrite LIVE, sl_rest_0. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact I|]. split; [exact I|].
    split; [exact H28|]. split; [reflexivity|].
    split; [apply sl_run_cap|]. split; [reflexivity|].
    intros Cp. destruct H26 as [(C0 & _)|(_ & _ & IN & _)]; [lc|].
    exact (sptr_of_spec L A OUT CAP (NODUP L A mem md HMR) IN). }
  rewrite H01.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    eapply (evt_normalize rsegs); [exact sb_wx | exact RO0 |].
    eapply sl_front with (lo := SP - 8368) (B := Bl) (r := CAP - NO) (junk := firstn (Z.to_nat (CAP - NO)) junk)
      (m := normalize rsegs mem) (cl := cl) (br := br) (dd := dd) (ei := ei) (nout := nout) (cap := cap) (out := out)
      (ev := ev).
    all: try first [exact MC | exact EL | exact H08 | exact ST0 | exact MI0 | exact BLn | exact H16 | exact H17
                   | exact H18 | exact H19 | exact CCLn | exact CBRn | exact CDDn | exact CEIn | exact COVn
                   | exact CERn' | exact HLG | exact HLE | exact HLF | exact sr_hem | exact sr_hl0 | exact sr_hop | lc].
    intros LV.
    destruct H26 as [(C0 & O0 & N0 & OE)|(Cp & NOle & IN & (F1 & F2 & FI) & OJ & LO' & LJ & LA)].
    - rewrite C0, O0, N0.
      split; [lc|]. split; [lc|]. split; [split; lc|]. split; [lc|]. split; [lc|]. split; [lc|].
      change (Z.to_nat (0 - 0)) with 0%nat. cbn [firstn].
      apply sl_cb_nil. lc.
    - assert (DA1 : SrOr (OUT + CAP <= 202912) (203000 <= OUT)).
      { assert (P : forall i, 0 <= i < 88 -> in_img Bm (202912 + i))
          by (intros i Hi; refine (proj1 (H12 (202912 + i) _)); unfold G_RELAY_LO, G_RELAY_HI; lc).
        unfold SrOr. destruct (sb_apart (in_img Bm) OUT CAP 202912 88 Cp ltac:(lia) FI P); lc. }
      assert (DA2 : SrOr (OUT + CAP <= 136740) (136744 <= OUT)).
      { assert (P : forall i, 0 <= i < 4 -> in_img Bm (136740 + i))
          by (intros i Hi; refine (proj1 (H13 (136740 + i) _)); unfold G_CLIENT; lc).
        unfold SrOr. destruct (sb_apart (in_img Bm) OUT CAP 136740 4 Cp ltac:(lia) FI P); lc. }
      assert (DA3 : SrOr (OUT + CAP <= ERR) (ERR + 4 <= OUT)).
      { assert (P : forall i, 0 <= i < 4 -> in_img Bm (ERR + i)) by (intros i Hi; apply H14; lc).
        unfold SrOr. destruct (sb_apart (in_img Bm) OUT CAP ERR 4 Cp ltac:(lia) FI P); lc. }
      split; [lc|]. split; [lc|].
      split; [split; [destruct DA1 as [X|X]; [left|right]; lc | destruct DA2 as [X|X]; [left|right]; lc]|].
      split; [destruct DA3 as [X|X]; [left|right]; lc|].
      split; [destruct LA as [X|X]; [left|right]; lc|].
      split; [lc|].
      rewrite firstn_all2 by lc.
      rewrite H01 in OJ. apply bytes_at_app in OJ as [_ JB]. rewrite LO' in JB.
      pose proof (sr_cb mem _ _ JB) as X. replace (length junk) with (Z.to_nat (CAP - NO)) in X by lc.
      apply (sb_rw_norm mem _ _ RO0).
      + apply X. intros i Hi. replace (OUT + NO + i) with (OUT + (NO + i)) by lc.
        refine (proj1 (block_facts Bm (aa_MR API) (aa_laws API) L A mem md OUT CAP (NO + i) HMR IN _)). lc.
      + intros i Hi. cbn in Hi. apply (ro_addr_out Bm H01); [lc|].
        replace (OUT + NO + i) with (OUT + (NO + i)) by lc. apply FI. lc. }
  intros ms1 (can1 & (s1 & HQ & REL & ROS) & EQ).
  destruct HQ as (jb & m1 & MU0 & WM0 & [(OFF & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3'
    & t4' & t5' & t6' & -> & STR)|(NOFF & CL3 & BR0 & [FIN|CALL])]).
  - apply SR_ret.
    exact (sr_off m1 ms1 can1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' OFF MU0 WM0 REL ROS EQ).
  - apply SR_ret.
    apply (XA sb_fin L A mem md 0%nat cap out [(SP - 112, SP)] ei 0 ev nout (CAP - NO) m1 ms1 can1 s1).
    + exact RO0.
    + exact (XA sb_rp_refl).
    + left. repeat split.
    + exact RES0.
    + exact H03.
    + exact NOFF.
    + intros _. repeat split.
    + intros _. split; [exact OB0|]. lc.
    + exact CCL.
    + intros lo hi [E|[]]. injection E as <- <-. left. lc.
    + exact MU0.
    + exact WM0.
    + exact FIN.
    + exact REL.
    + exact ROS.
    + exact EQ.
  - apply (sr_loop (S (Z.to_nat (2 * (NO + LEN) - CAP))) CAP); [lc|].
    apply (XA sb_next L A mem md 0%nat cap out [(SP - 112, SP)] jb ei 0 ev nout (CAP - NO) m1 ms1 can1 s1).
    + exact RO0.
    + exact (XA sb_rp_refl).
    + left. repeat split.
    + exact RES0.
    + exact H03.
    + exact NOFF.
    + intros _. split; [exact OB0|]. lc.
    + exact CCL.
    + intros lo hi [E|[]]. injection E as <- <-. left. lc.
    + exact MU0.
    + exact WM0.
    + exact CALL.
    + exact REL.
    + exact ROS.
    + exact EQ.
Qed.

End Main.

Theorem send_line_holds (F : ResFormT) : memcpy_contract -> __errno_location_contract ->
  realloc_contract_rt Bm API F 0x178f8 -> realloc_null_contract_rt Bm API F 0x178f8 -> ms_malloc Bm = 0x1608c ->
  send_line_contract Bm API F.
Proof using All.
  intros MC EL RA RN HMPC. unfold send_line_contract. cbv zeta.
  intros L A regs mem md bnd Bl O junk cl br dd ei mx nout cap out ev
    H01 H02 H03 H04 H04a H05 H06 H07 H08 H09 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27
    H28 H29.
  exact (sr_main F MC EL RA RN L A regs mem md bnd Bl O junk cl br dd ei mx nout cap out ev
    H01 H02 H03 H04 H04a H05 H06 H07 H08 H09 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27
    H28 H29 HMPC).
Qed.

End SB.
