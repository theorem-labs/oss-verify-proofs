(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, image B's (fuzz_reply.asan-ubsan) block `order` of SEG_EXIT of
   LLVMFuzzerTestOneInput: lx_order, the statement lib/B/W_bx_defs.v lx_order_S fixes.  Ported from the proved A donor
   b86949b953d lib/A/W_LLVMFuzzerTestOneInput_exit.v:574-1781 (the lxo_ table lemmas, the
   lxk_ kept lemmas of :679-1078, lxo_loop and lx_order), with every register, offset, object and fact re-read from
   B's objdump (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record), 0x84e64-0x84f00):
     0x84e64  auipc a0 / lw s3 = g_nsrc (B's listing: PHi 81 / PLdHi x19 x10 81, object A_OBJ 4; no g_nsrc high half
              in a register); sd zero -> at (F+208); blez s3 -> 0x84fe0;
     0x84e74  ld a1 = g_src (PLdHi x11 x18 70, A_OBJ 5, through s2 = HI_G_SRC); s3 = min(g_nsrc - 1, 3) + 1;
              a2 = snez g_src, a0 = g_src & 7, a3 = seqz a0 & a2 (the UBSan flags; the runner folds both to 1 from
              g_src's atom facts, W_traps.v's recipe R1); a4 = F+192; a5 = s3; a6 = a0 = g_src;
     0x84eac  the copy loop (lxo_loop, by induction on the trips left): three UBSan trap branches to unimp 0x850fc -
              `bltu a0,a1` (the pointer wrap, a0 = g_src + 56 i: refuted with W_traps.v trap_ptr_bltu), `seqz a7,a0;
              xor a7,a2,a7; beqz a7` (null consistency: the runner folds seqz to 0, refuted with trap_null_xor_folded
              on a2 = 1) and `beqz a3` (base aligned and not null: decided by the runner from the seat's fact a3 = 1,
              recipe R3) - then the inline ASan check of the 4-byte read (srli; add s11; lb; bnez: decided from the
              loop's shadow entry), `lw a7,0(a6)`, a0 += 56, a6 += 56, a5 -= 1, `sw a7,0(a4)` (order[i] at
              F+192+4i), a4 += 4, `bnez a5` back, `j 0x84f00`.
   SB is in s11 (x27).  The traps' facts (g_src not null, 16-aligned, g_src + 56 i <= g_src + 896 below the
   allocation ceiling) come from the table block: arelay_at names (g_src, ATABLE) a live block, so AR's al_blocks
   bounds it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_shadow_pin W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section lx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Local Notation LLVMF_STK := YCfn.LLVMF_STK.
Variable B : asyms. Variable MT : ameter_ops. Variables XM_LIB XN_LIB : Z -> Z. Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop. Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop. Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop. Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable MMAX : Z.
(* W_LLVMFuzzerTestOneInput_exit.v's Section lx hypotheses this block uses, verbatim *)
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Hypothesis TL : PALib B.

(* the symbolic-run scaffolding *)
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
Definition lxo_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* ---- the relay's table in memory: entry i's 4-byte fd field, from atable_at (donor :576-673) ---- *)
Lemma lxo_ent_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.
Lemma lxo_cc_len : forall es,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat length]. rewrite length_app, lxo_ent_len, IH by assumption. lia.
Qed.
Lemma lxo_cc_nth : forall es i k d,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (i < length es)%nat -> (k < 56)%nat ->
  nth (56 * i + k) (concat (map entry_bytes es)) d = nth k (entry_bytes (nth i es lxo_e0)) d.
Proof.
  induction es as [|e es IH]; intros i k d HF Hi Hk; cbn [length] in Hi; [lia|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat]. destruct i as [|i].
  - replace (56 * 0 + k)%nat with k by lia. cbn [nth].
    apply app_nth1. rewrite lxo_ent_len by assumption. exact Hk.
  - rewrite app_nth2 by (rewrite lxo_ent_len by assumption; lia).
    rewrite lxo_ent_len by assumption.
    replace (56 * S i + k - 56)%nat with (56 * i + k)%nat by lia.
    cbn [nth]. apply IH; [exact HF | lia | exact Hk].
Qed.
Lemma lxo_nth_le_bytes : forall n z k d, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k d Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma lxo_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0)) = YO0f.le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold Mem.le4. rewrite lxo_nth_le_bytes by exact Hk.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 v) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by exact Hv. reflexivity.
Qed.
Lemma lxo_le_byte1 : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by exact Hr. reflexivity.
Qed.
Lemma lxo_nth_bzs : forall l n, nth n (bzs l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  unfold bzs. induction l as [|b l IH]; intros [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.
Lemma lxo_tbl_fd : forall (W : world segs) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (i : nat),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  (i < length es)%nat ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat i) 4 (re_fd (nth i es lxo_e0)).
Proof.
  intros W mem G es tail i [_ [_ Hg]] Hpad Hfd Hi.
  assert (Hv : 0 <= re_fd (nth i es lxo_e0) < 2 ^ 31).
  { rewrite Forall_forall in Hfd. apply Hfd. apply nth_In. exact Hi. }
  pose proof (lxo_cc_len es Hpad) as Hcl.
  unfold val_mem. intros k Hk.
  assert (Hj : (56 * i + k < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
  { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
  unfold garr8 in Hg. destruct (Hg _ Hj) as [Hb _]. unfold val_mem in Hb.
  specialize (Hb 0%nat ltac:(lia)).
  replace (G + AENT * Z.of_nat i + Z.of_nat k) with (G + Z.of_nat (56 * i + k) + Z.of_nat 0)
    by (unfold AENT; lia).
  rewrite Hb. f_equal.
  assert (Hn : nth (56 * i + k) (bzs (concat (map entry_bytes es) ++ tail)) 0 =
               bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 (re_fd (nth i es lxo_e0)))) (Z_to_bv 8 0))).
  { rewrite lxo_nth_bzs. f_equal.
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite lxo_cc_nth by (first [exact Hpad | exact Hi | lia]).
    unfold entry_bytes. rewrite app_nth1 by (rewrite Mem.length_le4; exact Hk). reflexivity. }
  rewrite Hn, lxo_le_byte1.
  apply bv_eq. rewrite Z_to_bv_unsigned, lxo_le4_byte by lia.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma lxo_pads_of_relay : forall ly S W mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es /\
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es.
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  split; rewrite Forall_forall in HE |- *; intros e He;
    destruct (HE e He) as (_ & _ & H3 & H4 & H5 & _); [split; assumption | exact H5].
Qed.

(* ---- the transport kit (donor :675-1078, the lxk_ lemmas the block uses), with B's globals fr_RG = fr_globals_b
   and B's aframe_at (no `full` flag) ---- *)
Definition LXK_CEIL8 : Z := alloc_ceiling + 8.
Definition lxk_fp_low (fp : list (Z * Z)) : Prop := Forall (fun r => 0 <= fst r /\ snd r <= LXK_CEIL8) fp.
Lemma lxk_ceil_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof asan_consts as (C1 & _). lia. Qed.
(* a bound on a range of fuzz_reply.asan-ubsan's globals, or on errno from the premises *)
Ltac lxk_low :=
  cbn [fst snd gfp]; unfold LXK_CEIL8 in *;
  cbn [fr_RG fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof lxk_ceil_lo; lia.
Lemma lxk_fp_low_nil : lxk_fp_low []. Proof. constructor. Qed.
Lemma lxk_fp_low_cons : forall r fp, 0 <= fst r -> snd r <= LXK_CEIL8 -> lxk_fp_low fp -> lxk_fp_low (r :: fp).
Proof. intros r fp H1 H2 H3. constructor; [split; assumption | exact H3]. Qed.
Lemma lxk_fp_low_app : forall f1 f2, lxk_fp_low f1 -> lxk_fp_low f2 -> lxk_fp_low (f1 ++ f2).
Proof. intros f1 f2 H1 H2. apply Forall_app. split; assumption. Qed.
Lemma lxk_fp_low_forall : forall fp, lxk_fp_low fp <-> (forall r, In r fp -> 0 <= fst r /\ snd r <= LXK_CEIL8).
Proof. intros fp. unfold lxk_fp_low. apply Forall_forall. Qed.
Lemma lxk_akept_of_low : forall (W : world segs) mem (W' : world segs) mem' fp,
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) -> lxk_fp_low fp -> akept W mem W' mem' fp.
Proof.
  intros W mem W' mem' fp HK Hl r Hr a Ha. rewrite lxk_fp_low_forall in Hl.
  destruct (Hl r Hr) as [H1 H2]. apply HK. lia.
Qed.
(* a live block: its bytes, and the 7 bytes of alignment slack a key's text may carry past them *)
Lemma lxk_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
Lemma lxk_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma lxk_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma lxk_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, lxk_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma lxk_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.

(* ---- struct list ---- *)
Lemma lxk_alist : forall ly S (W : world segs) mem md LA l lines,
  AR segs B ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= LXK_CEIL8 ->
  lxk_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : lxk_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite lxk_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (lxk_blk ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lxk_bzs_len, length_app. cbn [length].
      unfold LXK_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply lxk_fp_low_cons; [cbn; lia | cbn; lia|]. apply lxk_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply lxk_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lxk_fp_low_cons; [cbn; lia | | apply lxk_fp_low_nil].
    cbn [gfp fst snd]. rewrite lxk_bzs_len, length_app, lxk_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold LXK_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- struct source ---- *)
Lemma lxk_asrc : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= LXK_CEIL8 ->
  lxk_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (lxk_alist ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (lxk_alist ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (lxk_alist ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (lxk_blk ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply lxk_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply lxk_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite lxk_bzs_len, Hpj. unfold APARTIAL, LXK_CEIL8 in *. lia.
    + apply lxk_fp_low_app; [exact A1|]. apply lxk_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* ---- one source_t of the relay's table ---- *)
Lemma lxk_aentry : forall ly S (W : world segs) mem md e,
  AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  lxk_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : lxk_fp_low (map (fun k => gfp (gestures_end_b_c.key_addr k)
                  (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (gestures_end_b_c.key_addr k,
                     Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite lxk_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (lxk_blk ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lxk_bzs_len, length_app. cbn [length].
      unfold LXK_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply lxk_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply lxk_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply lxk_fp_low_cons; [cbn; lia | | apply lxk_fp_low_nil].
      cbn [gfp snd]. rewrite lxk_bzs_len, length_app. unfold LXK_CEIL8 in *. lia.
    + apply lxk_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite lxk_bzs_len, lxk_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold LXK_CEIL8. pose proof lxk_ceil_lo. lia. }
        destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold LXK_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan-ubsan's globals ---- *)
Lemma lxk_arelay : forall ly S (W : world segs) mem md G es,
  AR segs B ly S W mem md -> arelay_at B fr_RG ly S W mem G es ->
  lxk_fp_low (arelay_fp fr_RG G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (lxk_blk ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : lxk_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite lxk_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (lxk_aentry ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite lxk_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (lxk_aentry ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply lxk_fp_low_cons; [lxk_low | lxk_low|].
    apply lxk_fp_low_cons; [lxk_low | lxk_low|].
    apply lxk_fp_low_cons; [lxk_low | lxk_low|].
    apply lxk_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, LXK_CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
Lemma lxk_aout : forall ly S (W : world segs) mem md c O mx no cap out,
  AR segs B ly S W mem md -> aout_at B fr_RG ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= LXK_CEIL8 ->
  lxk_fp_low (aout_fp B fr_RG cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply lxk_fp_low_cons; [lxk_low | lxk_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply lxk_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lxk_fp_low_cons; [cbn; lia | cbn; unfold LXK_CEIL8 in *; lia | apply lxk_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
Lemma lxk_akept_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= LXK_CEIL8 ->
  akept W mem W' mem' [(lo, hi)].
Proof.
  intros W W' mem mem' lo hi HK H1 H2. apply lxk_akept_of_low; [exact HK|].
  apply lxk_fp_low_cons; [cbn; lia | cbn; lia | apply lxk_fp_low_nil].
Qed.
Lemma lxk_akept_of_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= LXK_CEIL8 ->
  forall x, lo <= x < hi -> abyte_kept W mem W' mem' x.
Proof. intros W W' mem mem' lo hi HK H1 H2 x Hx. apply HK. lia. Qed.
Lemma lxk_amodel_kept : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= LXK_CEIL8 ->
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG, fr_globals_b; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= LXK_CEIL8)
      by (unfold fr_RG, fr_globals_b, LXK_CEIL8; cbn; unfold ASRC; pose proof lxk_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (lxk_asrc ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (lxk_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (lxk_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (lxk_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (lxk_arelay ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3
             (lxk_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (lxk_aout ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (lxk_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5).
    apply lxk_akept_rng; [exact KEEP | lxk_low | lxk_low]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6).
    apply lxk_akept_rng; [exact KEEP | lxk_low | lxk_low]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply lxk_akept_rng; [exact KEEP | lxk_low | lxk_low]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, LXK_CEIL8 in *. pose proof lxk_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, LXK_CEIL8 in *. pose proof lxk_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, LXK_CEIL8 in *. pose proof lxk_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, LXK_CEIL8 in *. pose proof lxk_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, LXK_CEIL8 in *. pose proof lxk_ceil_lo. lia.
Qed.
Lemma lxk_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
Lemma lxk_ainput_kept : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR segs B ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold LXK_CEIL8. lia.
Qed.
Lemma lxk_rom_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  rom_view segs W' mem'.
Proof.
  intros W W' mem mem' HR KEEP a Ha. rewrite <- (HR a Ha).
  assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
  pose proof (pa_segs_low a Hin) as Hlow. pose proof lxk_ceil_lo.
  exact (proj1 (KEEP a ltac:(unfold LXK_CEIL8, kLowMemEnd in *; lia))).
Qed.
Lemma lxk_jt_kept : forall (W W' : world segs) mem mem',
  jt_rom W mem -> (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HJ KEEP i Hi. apply (akept_vm W mem); [|exact (HJ i Hi)].
  intros x Hx. apply KEEP. unfold fr_jtab, LXK_CEIL8 in *. pose proof lxk_ceil_lo. cbn in Hx. lia.
Qed.
(* B's frame (no `full`: every slot holds from the prologue on) across runs whose only stores are order[0..4) and
   `at`, [F+192, F+216) *)
Lemma lxk_aframe_kept : forall cx FF (W W' : world segs) mem mem',
  aframe_at cx FF W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) -> abyte_kept W mem W' mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  LXK_CEIL8 <= lf_F cx -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= LXK_CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= LXK_CEIL8 ->
  aframe_at cx FF W' mem'.
Proof.
  intros cx FF W W' mem mem'
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 &
     A20 & A21 & A22)
    HK WK HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof lxk_ceil_lo as HCL. unfold LXK_CEIL8 in *.
  assert (KW : forall a n, awr W mem a n -> awr W' mem' a n) by (intros a n Hw i Hi; apply WK; exact (Hw i Hi)).
  assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= lf_F cx + 192 \/ lf_F cx + 216 <= a) ->
             sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 H2 Hv. apply (lxk_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply HK; lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | exact (A1 o r Hin)]. }
  split; [exact (KW _ _ A2)|].
  do 17 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split; [exact (KW _ _ A20)|].
  split; [|exact (KW _ _ A22)].
  apply (akept_garr8 W mem); [|exact A21]. intros x Hx.
  unfold fake_shadow in Hx. cbn [length] in Hx. apply HK; lia.
Qed.
(* everything the block's post says of the memory, carried across runs whose only stores are order[0..4) and `at` *)
Lemma lxk_carry : forall cx (W : world segs) mem mem' md ly3 S3 fpos m,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx W mem mem' md ly3 S3 fpos m HAR Hfin Hlen Hsp HFR HMOD HIN HRV HJT KEEP WK.
  pose proof lxk_ceil_lo as HCL. pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold LXK_CEIL8 in *; lia. }
  split.
  { apply (lxk_aframe_kept cx _ W W mem mem' HFR KEEP WK); unfold LXK_CEIL8, SB in *; lia. }
  split; [exact (lxk_amodel_kept ly3 S3 W mem md W mem' m HAR HMOD HE0
                   ltac:(unfold LXK_CEIL8, kLowMemEnd in *; lia) KL)|].
  split; [exact (lxk_ainput_kept cx ly3 S3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (lxk_rom_kept W W mem mem' HRV KL)|].
  exact (lxk_jt_kept W W mem mem' HJT KL).
Qed.
(* the fake frame's flag word FF + 120 across the same runs: the fake frame lies below the allocation ceiling *)
Lemma lxk_flag_kept : forall cx (W : world segs) mem mem' md ly3 S3 fpos,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) -> abyte_kept W mem W mem' a) ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros cx W mem mem' md ly3 S3 fpos HAR Hfin Hsp KEEP HFL.
  pose proof lxk_ceil_lo as HCL.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  apply (lxk_sv8_kept W W mem mem'); [|exact HFL]. intros x Hx. apply KEEP; lia.
Qed.

(* ---- the image facts the block reads, by vm_compute on the pinned placement: s2 = HI_G_SRC is auipc slot 70, g_src
   is A_OBJ 5 (0x5d8d40 = HI_G_SRC + 1892), g_nsrc is A_OBJ 4 (0x5d8d20, read at 0x84e68 through auipc slot 81) ---- *)
Lemma lxo_hi : VAL (A_HI 70) = HI_G_SRC /\ VAL (A_OBJ 5) = rg_src fr_RG /\ VAL (A_OBJ 4) = rg_nsrc fr_RG.
Proof. vm_compute. split; [reflexivity | split; reflexivity]. Qed.

(* ---- the symbolic state at AF_LLVM_exit (0x84e64): the store `at` = 0 (s1+208, the one writable region), g_nsrc read
   by the listing's PLdHi slot at 0x84e68 (A_OBJ 4, through a0 = auipc slot 81), g_src read by the PLdHi slot at
   0x84e74 through s2 = auipc slot 70 (so s2 holds its A_HI atom).  Atoms: 32 = g_nsrc, 33 = g_src; R1 on 33. ---- *)
Definition xo_extra (lenz G : Z) : list word := map (Z_to_bv 64) [lenz; G].
Definition xo_sr : list sv := sr_set sr_atoms 18 (SOff (A_HI 70) 0).
Definition xo_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 208 216 208 216 [];
    YP09.mkRegion (Some (A_OBJ 4)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
    YP09.mkRegion (Some (A_OBJ 5)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))] ].
Definition xo_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 16 0);
            (33%nat, mkAF 4096 140737479966720 4) ] [] [].
Definition ss_x : sstate := mkSS AF_LLVM_exit xo_sr xo_regions None xo_facts.
Definition xo_Bx : sv := SOff 27 0.
Definition xo_SH : list shent := (@nil shent).
(* the registers lregs_X names that the block does not write (s2 holds an image atom, read with prreg) *)
Definition XO_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 26; 27]%bv.
(* a run's write obligation: `at` is in the function's own stack window, the other regions are read-only *)
Ltac xo_awr U9 :=
  cbn [ss_mem add_cond ss_x xo_regions];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold YCfn.LLVMF_STK; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside `at` is outside every region's writable window *)
Ltac xo_nowr U9 Hna :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_x xo_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr; lia | ]);
  destruct Hin.

(* ================================================================== the order[] copy loop (0x84eac)
   One trip: `bltu a0,a1` (the pointer-wrap trap: a0 = G + 56 i >= a1 = G, refuted with trap_ptr_bltu); `seqz a7,a0;
   xor a7,a2,a7; beqz a7` (null consistency: refuted with trap_null_xor_folded on a2 = 1) and `beqz a3` (base aligned
   and not null: decided by the runner from a3 = 1); the ASan check of T[i] (srli a7,a0,3; add a7,a7,s11;
   lb a7,0(a7): 0 inside the table's block, so bnez falls through); lw a7,0(a6) (T[i].fd); a0 += 56; a6 += 56;
   a5 -= 1; sw a7,0(a4) (order[i]); a4 += 4; bnez a5 -> head; j 0x84f00.
   The head's state: a0 = &T[i] (atom 10; a6 pinned to it), a1 = G (atom 11), a2 = a3 = 1 (atoms 12, 13, R3), a4 =
   &order[i] (atom 14, the one writable region), a5 = trips left (atom 15), s11 = SB (atom 27); atom 32 = T[i].fd. *)
Definition LXO_KEPT : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition lxo_sr : list sv := sr_set sr_atoms 16 (SOff 10 0).
Definition lxo_regions : smem :=
  [ YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
    YP09.mkRegion (Some 14%nat) 0 4 0 4 [] ].
Definition lxo_facts : facts :=
  mkFacts [ (10%nat, mkAF 4096 140737479966720 3); (11%nat, mkAF 4096 140737479966720 3);
            (12%nat, mkAF 1 1 0); (13%nat, mkAF 1 1 0); (14%nat, mkAF (2 ^ 46) (2 ^ 47) 0);
            (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 (2 ^ 31 - 1) 0) ] [] [].
Definition ss_lxo : sstate := mkSS AX_order lxo_sr lxo_regions None lxo_facts.
Definition lxo_SH : list shent := [ mkSHE 10 0 8 ].
Definition lxo_Bx : sv := SOff 27 0.
Definition lxo_extra (fd : Z) : list word := map (Z_to_bv 64) [fd].
(* a run's write obligation: the order cell is in the caller's stack window, the table entry is read-only *)
Ltac lxo_awr U14 :=
  cbn [ss_mem add_cond ss_lxo lxo_regions];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U14 in Ha;
      first [ lia | left; split; [left; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the order cell is outside every region's writable window *)
Ltac lxo_nowr U14 Hna :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_lxo lxo_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U14 in Hr; lia | ]);
  destruct Hin.
Lemma lxo_add_lit : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
(* a byte present before a run that only grows the memory is present after it *)
Lemma lxo_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.

Lemma lxo_loop : forall (kn : nat) (i norder G F : Z) (es : list rentry)
    W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  Z.of_nat kn = norder - i -> 0 <= i < norder -> norder <= 4 ->
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (G, ATABLE) (ablocks B lyc Sc) ->
  (forall q, i <= q < norder -> 0 <= re_fd (nth (Z.to_nat q) es lxo_e0) < 2 ^ 31) ->
  (forall q, i <= q < norder ->
     val_mem segs (arm W memc) (G + AENT * q) 4 (re_fd (nth (Z.to_nat q) es lxo_e0))) ->
  alloc_ceiling < F -> sp0 - STK <= F + 192 -> F + 208 <= sp0 -> sp0 <= 2 ^ 47 ->
  awr W memc (F + 192) 16 ->
  getr regs 10 = w64 (G + AENT * i) -> getr regs 11 = w64 G ->
  getr regs 12 = w64 1 -> getr regs 13 = w64 1 ->
  getr regs 14 = w64 (F + 192 + 4 * i) -> getr regs 15 = w64 (norder - i) ->
  getr regs 16 = w64 (G + AENT * i) -> getr regs 27 = w64 SB ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AX_order)) memc (seg_rom segs)) mdc)
  (fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AX_join)) mem' (seg_rom segs)) md' /\
    ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
    (forall r, In r LXO_KEPT -> getr regs' r = getr regs r) /\
    (forall q, i <= q < norder ->
       val_mem segs (arm W mem') (F + 192 + 4 * q) 4 (re_fd (nth (Z.to_nat q) es lxo_e0))) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * norder) ->
       aview segs (w_H W) mem' a = aview segs (w_H W) memc a) /\
    (forall a, writable_at segs (arm W memc) a -> writable_at segs (arm W mem') a)).
Proof.
  (* as in lx_order below: keep the lemma's arguments to B G_fr LAWS HG *)
  clear XN_LIB XM_LIB RLO RHI fr_live_pre fr_live_post fr_surv fr_FP LS RINV MMAX MT TL.
  intros kn. induction kn as [|kn IH];
    intros i norder G F es W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k
      Hkn Hi Hn4 HJ HGin Hfdr Hfdv HFc HSTK HFsp Hsp47 HAW R10 R11 R12 R13 R14 R15 R16 R27.
  { exfalso. lia. }
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HAR : AR segs B lyc Sc W memc mdc) by (eapply ajournal_gx_AR; exact HJ).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc G ATABLE HAR HGin) as (HP16 & HP4096 & HPceil & HPapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity.
  rewrite RQ in HPceil.
  assert (HGF : G + 896 <= F + 192) by lia.
  assert (G8 : G = 8 * (G / 8)).
  { pose proof (Z.div_mod G 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
    rewrite D at 2. replace (16 * (G / 16)) with ((2 * (G / 16)) * 8) by ring.
    rewrite Z.div_mul by lia. lia. }
  assert (GI8 : (G + 56 * i) mod 8 = 0).
  { rewrite G8. replace (8 * (G / 8) + 56 * i) with ((G / 8 + 7 * i) * 8) by ring. apply Z_mod_mult. }
  assert (G08 : G mod 8 = 0).
  { rewrite G8. replace (8 * (G / 8)) with ((G / 8) * 8) by ring. apply Z_mod_mult. }
  pose proof (Hfdv i ltac:(lia)) as Mu. pose proof (Hfdr i ltac:(lia)) as Hfdb.
  unfold AENT in Mu, Hfdv, R10, R16.
  (* ---- the head's state ---- *)
  remember (Eimg (Ereg regs (lxo_extra (re_fd (nth (Z.to_nat i) es lxo_e0))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (lxo_extra (re_fd (nth (Z.to_nat i) es lxo_e0)))) E)
    by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hm).
  assert (E10 : ew E 10 = Z_to_bv 64 (G + 56 * i)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E11 : ew E 11 = Z_to_bv 64 G) by (rewrite (EEo 11%nat 11%bv eq_refl); exact R11).
  assert (E12 : ew E 12 = Z_to_bv 64 1) by (rewrite (EEo 12%nat 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = Z_to_bv 64 1) by (rewrite (EEo 13%nat 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = Z_to_bv 64 (F + 192 + 4 * i)) by (rewrite (EEo 14%nat 14%bv eq_refl); exact R14).
  assert (E15 : ew E 15 = Z_to_bv 64 (norder - i)) by (rewrite (EEo 15%nat 15%bv eq_refl); exact R15).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_fd (nth (Z.to_nat i) es lxo_e0)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U10 : bv_unsigned (ew E 10) = G + 56 * i) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U14 : bv_unsigned (ew E 14) = F + 192 + 4 * i) by (rewrite E14; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E ss_lxo
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_order)) memc (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_lxo. apply pa_entry_st_ok_full.
    - unfold lxo_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]; rewrite <- HE.
      rewrite R16. apply bv_eq. fold (U E (SOff 10 0)). rewrite (U_atom E 10 _ E10) by lia.
      unfold w64. apply unsigned_lit_small. lia.
    - vm_compute. reflexivity.
    - unfold lxo_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (G + 56 * i) 0 4 (SOff 32 0) (re_fd (nth (Z.to_nat i) es lxo_e0)));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mu.
      + rewrite U14. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. replace (F + 192 + 4 * i + o) with (F + 192 + (4 * i + o)) by lia.
        apply HAW. lia.
    - unfold lxo_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10, U14.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [lxo_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E10, E11, E12, E13, E14, E27, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia); assumption. }
  clear HE.
  assert (HBx : U E lxo_Bx = SHADOW_OFF)
    by (unfold lxo_Bx; rewrite (U_atom E 27 SB E27) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs lxo_Bx lxo_SH E (mrestrict (w_H W) memc)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    + apply (range_addressable_of_block segs B LAWS lyc Sc W memc mdc G ATABLE (G + 56 * i) 8 HAR HGin);
        rewrite ?RQ; lia.
    + exact HBx.
    + rewrite (U_atom E 10 _ E10) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- 0x84eac bltu a0,a1: the UBSan pointer-wrap trap, never taken (a0 = G + 56 i >= a1 = G) ---- *)
  psrr_branch_tok RUN BR HS SHOK lxo_Bspan.
  { exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
      rewrite (trap_ptr_bltu E (SOff 11 0) (SOff 10 0) G (G + 56 * i)) in Hc;
        [discriminate Hc | apply U_atom; [exact E11 | lia] | apply U_atom; [exact E10 | lia] | lia] end. }
  lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end.
  (* ---- 0x84eb0-0x84eb8: seqz a7,a0 (the runner folds it to 0: a0 >= 4096); xor a7,a2,a7; to the beqz ---- *)
  paj_run_tok RUN HS HJ SHOK lxo_Bspan.
  { lxo_awr U14. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * i + 4) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); lxo_nowr U14 Hna).
  assert (P1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (lxo_pres_grows W _ _ a HG1 Hp)).
  clear HFr1 HG1.
  (* ---- 0x84eb8 beqz a7: the UBSan null-consistency trap, never taken (a2 = 1 xor 0); the next one, 0x84ebc beqz a3,
     the runner decides from the seat's fact a3 = 1 ---- *)
  psrr_branch_tok RUN BR HS SHOK lxo_Bspan.
  { exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
      rewrite (trap_null_xor_folded E 12 E12) in Hc; discriminate Hc end. }
  lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end.
  (* ---- one trip, to the bnez a5 at 0x84ee8 ---- *)
  paj_run_tok RUN HS HJ SHOK lxo_Bspan.
  { lxo_awr U14. }
  rename HFr into HFr2, HG0 into HG2. clear HF.
  (* the order cell i now holds T[i].fd; nothing else moved *)
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * i + 4) ->
      aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) memc a)
    by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (lxo_nowr U14 Hna);
        exact (K1 a Ha Hna)).
  assert (P2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a)
    by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
  clear HFr2 HG2 K1 P1.
  psrr_branch_tok RUN BR HS SHOK lxo_Bspan.
  - (* 0x84ee8 bnez taken: trips left, back to the head at i + 1 *)
    rewrite branch_ne_U, (U_atom_off E 15 _ (-1) E15), U_lit in Hc by lia.
    assert (Hlt : i + 1 < norder)
      by (destruct (Z.eqb_spec (norder - i + -1) 0); [discriminate | lia]).
    paj_run_to_tok RUNTO HS HJ SHOK lxo_Bspan AX_order.
    { lxo_awr U14. }
    rename HFr into HFr3, HG0 into HG3. clear HF.
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * i + 4) ->
        aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr3 a Ha) by (lxo_nowr U14 Hna);
          exact (K2 a Ha Hna)).
    assert (P3 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG3 (P2 a Hp))).
    clear HFr3 HG3.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
    assert (SV2 : val_mem segs (arm W (ms_mem ms1)) (F + 192 + 4 * i) 4 (re_fd (nth (Z.to_nat i) es lxo_e0))).
    { replace (F + 192 + 4 * i) with (F + 192 + 4 * i + 0) by lia.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 14%nat (F + 192 + 4 * i) _ _ _ _ _ 0 4%N (SOff 32 0) _ RG2) end.
      - exact U14.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ LXO_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (10%bv : bv 5) N10. prreg HS (14%bv : bv 5) N14.
    prreg HS (15%bv : bv 5) N15. prreg HS (16%bv : bv 5) N16.
    rewrite U10 in N10, N16. rewrite U14 in N14.
    rewrite E15, unsigned_lit_small in N15 by lia.
    pmkst HS.
    eapply SRr_mono.
    { apply (IH (i + 1) norder G F es W (ms_regs ms1) (ms_mem ms1) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k);
        [lia | lia | lia | exact HJ | exact HGin | intros q Hq; apply Hfdr; lia | | exact HFc | exact HSTK
        | exact HFsp | exact Hsp47 | | | | | | | | | ].
      - intros q Hq. apply (akept_vm W memc); [|apply Hfdv; lia].
        intros x Hx. unfold AENT in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. split.
        + apply K3; lia.
        + intros Hw. apply (writable_kept (w_H W) memc (ms_mem ms1) x); [apply P3 | exact Hw].
      - intros j Hj. apply (writable_kept (w_H W) memc (ms_mem ms1)); [apply P3 | apply HAW; exact Hj].
      - rewrite N10. unfold w64, AENT. f_equal. lia.
      - rewrite (KR 11%bv ltac:(cbv; tauto)). exact R11.
      - rewrite (KR 12%bv ltac:(cbv; tauto)). exact R12.
      - rewrite (KR 13%bv ltac:(cbv; tauto)). exact R13.
      - rewrite N14. unfold w64. f_equal. lia.
      - rewrite N15. unfold w64. f_equal. lia.
      - rewrite N16. unfold w64, AENT. f_equal. lia.
      - rewrite (KR 27%bv ltac:(cbv; tauto)). exact R27. }
    intros W' c' _ (-> & regs' & mem' & md' & Hc' & HJ' & KR' & HV' & HK' & HW').
    split; [reflexivity|]. exists regs', mem', md'.
    split; [exact Hc'|]. split; [exact HJ'|].
    split; [intros r Hr; rewrite (KR' r Hr); exact (KR r Hr)|].
    split.
    { intros q Hq. destruct (Z.eq_dec q i) as [-> | Hqi]; [|apply HV'; lia].
      apply (akept_vm W (ms_mem ms1)); [|exact SV2].
      intros x Hx. split; [apply HK'; lia | apply HW']. }
    split.
    { intros a Ha Hna. rewrite (HK' a Ha) by lia. apply K3; [exact Ha | lia]. }
    intros a Hw. apply HW'. apply (writable_kept (w_H W) memc (ms_mem ms1) a); [apply P3 | exact Hw].
  - (* 0x84ee8 bnez not taken: 0x84eec j 0x84f00 *)
    rewrite branch_ne_U, (U_atom_off E 15 _ (-1) E15), U_lit in Hc by lia.
    assert (Hend : i + 1 = norder)
      by (destruct (Z.eqb_spec (norder - i + -1) 0); [lia | discriminate]).
    paj_run_to_tok RUNTO HS HJ SHOK lxo_Bspan AX_join.
    { lxo_awr U14. }
    rename HFr into HFr3, HG0 into HG3. clear HF.
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * i + 4) ->
        aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr3 a Ha) by (lxo_nowr U14 Hna);
          exact (K2 a Ha Hna)).
    assert (P3 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG3 (P2 a Hp))).
    clear HFr3 HG3.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
    assert (SV2 : val_mem segs (arm W (ms_mem ms1)) (F + 192 + 4 * i) 4 (re_fd (nth (Z.to_nat i) es lxo_e0))).
    { replace (F + 192 + 4 * i) with (F + 192 + 4 * i + 0) by lia.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 14%nat (F + 192 + 4 * i) _ _ _ _ _ 0 4%N (SOff 32 0) _ RG2) end.
      - exact U14.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ LXO_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. apply SRr_ret.
    split; [reflexivity|].
    eexists _, _, _. split; [reflexivity|].
    split; [exact HJ|].
    split; [exact KR|].
    split; [intros q Hq; replace q with i by lia; exact SV2|].
    split; [intros a Ha Hna; apply K3; [exact Ha | lia]|].
    intros a Hw. apply (writable_kept (w_H W) memc (ms_mem ms1) a); [apply P3 | exact Hw].
Qed.

(* ================================================================== the block (0x84e64) *)
Lemma lx_order : lx_order_S B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP.
Proof.
  (* the run tactics fill some evars with any section variable of their type: clear the ones the statement does not
     name, so that the lemma's arguments are the statement's and LAWS HG TL *)
  clear XN_LIB fr_live_post fr_surv LS RINV MMAX.
  intros cx W c regs mem md own ly3 S3 k m fpos t HB Hc HJ Hown Hframe HFL Hmodel Hinput Hrom HregsX Hjt.
  subst c own.
  match goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  pose proof lxk_ceil_lo as HCL.
  pose proof HregsX as (R2 & R8 & R9 & R18 & R26 & R27 & R3 & R4 & Hkb).
  pose proof Hmodel as (Hhs4 & Hslots & Hrel & _).
  pose proof Hrel as (Hsrc & Hsrcw & Hnsrc & Hnsrcw & _ & _ & Hlen16 & HGin & (tl & Htbl) & _ & _).
  destruct (lxo_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) Hrel) as (HPAD & HFDS).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold YCfn.LLVMF_STK in Hslo.
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  destruct (al_blocks _ _ LAWS ly3 S3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  pose proof Hframe as (_ & HAWR & _).
  pose proof lxo_hi as (VH70 & VO5 & VO4).
  assert (VN : rg_nsrc fr_RG = 0x5d8d20) by reflexivity.
  assert (VG : rg_src fr_RG = 0x5d8d40) by reflexivity.
  (* ---- the join, shared by the two norder cases: the copy loop, then the post ---- *)
  assert (JOIN : forall regs1 mem1 md1,
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem1 md1 k ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
       aview segs (w_H W) mem1 a = aview segs (w_H W) mem a) ->
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
    val_mem segs (arm W mem1) (lf_F cx + AX_AT) 8 0 ->
    (0 < length (lm_es m))%nat ->
    getr regs1 10 = w64 (lm_G m) -> getr regs1 11 = w64 (lm_G m) ->
    getr regs1 12 = w64 1 -> getr regs1 13 = w64 1 ->
    getr regs1 14 = w64 (lf_F cx + 192) ->
    getr regs1 15 = w64 (Z.min (Z.of_nat (length (lm_es m))) 4) ->
    getr regs1 16 = w64 (lm_G m) -> getr regs1 19 = w64 (Z.min (Z.of_nat (length (lm_es m))) 4) ->
    (forall r, In r XO_KEPT -> getr regs1 r = getr regs r) -> getr regs1 18 = w64 HI_G_SRC ->
    SRr segs W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AX_order)) mem1 (seg_rom segs)) md1) POST).
  { intros regs1 mem1 md1 HJ1 K1 P1 SVA1 Hpos Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q19 KK1 Q18.
    assert (Hno : 0 < Z.min (Z.of_nat (length (lm_es m))) 4 <= 4) by lia.
    assert (Hnl : Z.min (Z.of_nat (length (lm_es m))) 4 <= Z.of_nat (length (lm_es m))) by lia.
    eapply SRr_mono.
    { apply (lxo_loop (Z.to_nat (Z.min (Z.of_nat (length (lm_es m))) 4)) 0
               (Z.min (Z.of_nat (length (lm_es m))) 4) (lm_G m) (lf_F cx) (lm_es m) W regs1 mem1 md1
               LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
               [(1, fpos)] ly3 S3 k);
        [ rewrite Z2Nat.id by lia; lia | lia | lia | exact HJ1 | exact HGin | | | lia
        | unfold YCfn.LLVMF_STK; lia | lia | lia | | | | | | | | | ].
      - intros q Hq. rewrite Forall_forall in HFDS. apply HFDS, nth_In. lia.
      - intros q Hq.
        pose proof (lxo_tbl_fd W mem (lm_G m) (lm_es m) tl (Z.to_nat q) Htbl HPAD HFDS ltac:(lia)) as Mq.
        rewrite Z2Nat.id in Mq by lia.
        apply (akept_vm W mem); [|exact Mq].
        intros x Hx. unfold AENT in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. split.
        + apply K1; lia.
        + intros Hw. apply (writable_kept (w_H W) mem mem1 x); [apply P1 | exact Hw].
      - intros j Hj. apply (writable_kept (w_H W) mem mem1); [apply P1|].
        replace (lf_F cx + 192 + j) with (lf_F cx + (192 + j)) by lia. apply HAWR. lia.
      - rewrite Q10. unfold AENT. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - exact Q11.
      - exact Q12.
      - exact Q13.
      - rewrite Q14. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - rewrite Q15. rewrite Z.sub_0_r. reflexivity.
      - rewrite Q16. unfold AENT. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - rewrite (KK1 27%bv ltac:(cbv; tauto)). exact R27. }
    intros W' c' _ (-> & regs' & mem' & md' & Hc' & HJ' & KR' & HV' & HK' & HW').
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a)
      by (intros a Hw; apply HW'; apply (writable_kept (w_H W) mem mem1 a); [apply P1 | exact Hw]).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) ->
        abyte_kept W mem W mem' a).
    { intros a Ha Hna. split; [|apply WK].
      rewrite (HK' a Ha) by lia. apply K1; [exact Ha | lia]. }
    destruct (lxk_carry cx W mem mem' md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                Hframe Hmodel Hinput Hrom Hjt KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2).
    pose proof (lxk_flag_kept cx W mem mem' md ly3 S3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    assert (KT : forall r, In r XO_KEPT -> getr regs' r = getr regs r).
    { intros r Hr. rewrite (KR' r); [apply KK1; exact Hr|].
      cbv [XO_KEPT In] in Hr. repeat (destruct Hr as [<- | Hr]; [cbv; tauto|]). destruct Hr. }
    unfold POST. split; [reflexivity|]. exists regs', mem', md'.
    split.
    { right. split; [rewrite Hc'; reflexivity|]. split; [exact Hpos|].
      split; [rewrite (KR' 19%bv ltac:(cbv; tauto)); exact Q19|].
      intros q Hq. unfold AX_ORDER. apply HV'. exact Hq. }
    split; [exact HJ'|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HJT2|].
    split.
    { apply (akept_vm W mem1); [|exact SVA1].
      intros x Hx. unfold AX_AT in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
      split; [apply HK'; lia | apply HW']. }
    unfold lregs_X.
    split; [rewrite (KT 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KT 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KT 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR' 18%bv ltac:(cbv; tauto)); exact Q18|].
    split; [rewrite (KT 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KT 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [rewrite (KT 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KT 4%bv ltac:(cbv; tauto)); exact R4|].
    exact Hkb. }
  (* ---- the entry state at 0x84e64 ---- *)
  remember (Eimg (Ereg regs (xo_extra (Z.of_nat (length (lm_es m))) (lm_G m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (xo_extra (Z.of_nat (length (lm_es m))) (lm_G m))) E)
    by (rewrite HE; split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hmm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hmm).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length (lm_es m))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (lm_G m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (EO4 : ew E (A_OBJ 4) = Z_to_bv 64 (rg_nsrc fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite VO4; reflexivity).
  assert (EO5 : ew E (A_OBJ 5) = Z_to_bv 64 (rg_src fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite VO5; reflexivity).
  (* A_HI 70 = atom 350, as prreg prints it *)
  assert (EH70 : ew E 350 = Z_to_bv 64 HI_G_SRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) VH70)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (UO4 : bv_unsigned (ew E (A_OBJ 4)) = rg_nsrc fr_RG)
    by (rewrite EO4; apply unsigned_lit_small; rewrite VN; lia).
  assert (UO5 : bv_unsigned (ew E (A_OBJ 5)) = rg_src fr_RG)
    by (rewrite EO5; apply unsigned_lit_small; rewrite VG; lia).
  assert (HS : st_ok_pi segs VAL E ss_x
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_exit)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_x. apply pa_entry_st_ok_full.
    - unfold xo_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]; rewrite <- HE.
      rewrite R18. apply bv_eq. fold (U E (SOff (A_HI 70) 0)).
      rewrite (U_img_atom E HEI (A_HI 70)) by (unfold A_HI, A_TEXT, A_LIM; lia).
      rewrite VH70. unfold w64. apply unsigned_lit_small. unfold HI_G_SRC; lia.
    - vm_compute. reflexivity.
    - unfold xo_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HAWR o ltac:(lia)).
      + rewrite UO4. split; [rewrite VN; lia|]. split; [rewrite VN; lia|].
        split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_nsrc fr_RG) 0 4 (SOff 32 0) (Z.of_nat (length (lm_es m))));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Hnsrc.
      + rewrite UO5. split; [rewrite VG; lia|]. split; [rewrite VG; lia|].
        split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_src fr_RG) 0 8 (SOff 33 0) (lm_G m));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Hsrc.
    - unfold xo_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, UO4, UO5, VN, VG.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [xo_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E27, E32, E33, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  assert (SHOK : sh_ok segs xo_Bx xo_SH E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_exit)) with (Z_to_bv 64 (BASE + AF_LLVM_exit)).
  (* ---- 0x84e64-0x84e70: auipc a0; lw s3 = g_nsrc; sd zero -> at (F+208); to the blez ---- *)
  paj_run_tok RUN HS HJ SHOK lxo_Bspan.
  { xo_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); xo_nowr U9 Hna).
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (lxo_pres_grows W _ _ a HG1 Hp)).
  clear HFr1 HG1.
  assert (S32 : bv_signed (sv_denot E (SOff 32 0)) = Z.of_nat (length (lm_es m))).
  { assert (U32 : U E (SOff 32 0) = Z.of_nat (length (lm_es m))) by (apply U_atom; [exact E32 | lia]).
    unfold U in U32. rewrite bv_signed_small; [exact U32 | rewrite U32; lia]. }
  assert (S0 : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity.
  (* ---- blez s3: g_nsrc <= 0 ---- *)
  psrr_branch_tok RUN BR HS SHOK lxo_Bspan.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc.
    apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m) = 0%nat) by lia.
    (* 0x84fe0 *)
    paj_run_to_tok RUNTO HS HJ SHOK lxo_Bspan AX_noord.
    { xo_awr U9. }
    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (xo_nowr U9 Hna);
          exact (K1 a Ha Hna)).
    assert (P2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
    clear HFr2 HG2.
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a)
      by (intros a Hw; apply (writable_kept (w_H W) mem (ms_mem ms0) a); [apply P2 | exact Hw]).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) ->
        abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [apply K2; [exact Ha | lia] | apply WK]).
    destruct (lxk_carry cx W mem (ms_mem ms0) md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                Hframe Hmodel Hinput Hrom Hjt KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2).
    pose proof (lxk_flag_kept cx W mem (ms_mem ms0) md ly3 S3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    assert (SVA : val_mem segs (arm W (ms_mem ms0)) (lf_F cx + AX_AT) 8 0).
    { unfold AX_AT.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 208 8%N (SLit 0) 0 RG0) end.
      - exact U9.
      - left. reflexivity.
      - reflexivity.
      - zside.
      - zside. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ XO_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (18%bv : bv 5) Q18. rewrite EH70 in Q18.
    pmkst HS. apply SRr_ret.
    unfold POST. split; [reflexivity|]. eexists _, _, _.
    split; [left; split; [reflexivity | exact Hn0]|].
    split; [exact HJ|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HJT2|]. split; [exact SVA|].
    unfold lregs_X.
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [exact Q18|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    exact Hkb.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc.
    apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    (* 0x84e74-0x84e88: ld a1 = g_src (PLdHi through s2), s3 = g_nsrc - 1, a3 = 3, a2 = snez a1, a0 = a1 & 7; to the
       bltu *)
    paj_run_tok RUN HS HJ SHOK lxo_Bspan.
    { xo_awr U9. }
    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (xo_nowr U9 Hna);
          exact (K1 a Ha Hna)).
    assert (P2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
    clear HFr2 HG2.
    (* ---- bltu s3, a3 (0x84e88): g_nsrc - 1 < 3, so norder = min(g_nsrc, 4); the runner folded a2 = snez g_src and
       a3 = seqz (g_src & 7) & a2 to 1 from atom 33's facts (W_traps.v's R1) ---- *)
    psrr_branch_tok RUN BR HS SHOK lxo_Bspan.
    + rewrite branch_ltu_U, (U_atom_off E 32 _ (-1) E32), U_lit in Hc0 by lia.
      apply Z.ltb_lt in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK lxo_Bspan AX_order.
      { xo_awr U9. }
      rename HFr into HFr3, HG0 into HG3. clear HF.
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
          aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a)
        by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr3 a Ha) by (xo_nowr U9 Hna);
            exact (K2 a Ha Hna)).
      assert (P3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
        by (intros a Hp; exact (lxo_pres_grows W _ _ a HG3 (P2 a Hp))).
      clear HFr3 HG3.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      assert (SVA : val_mem segs (arm W (ms_mem ms1)) (lf_F cx + AX_AT) 8 0).
      { unfold AX_AT.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 208 8%N (SLit 0) 0 RG0) end.
        - exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ XO_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
      prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14. prreg HS (15%bv : bv 5) N15.
      prreg HS (16%bv : bv 5) N16. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
      pmkst HS.
      apply JOIN.
      * exact HJ.
      * exact K3.
      * exact P3.
      * exact SVA.
      * lia.
      * rewrite N10, E33. reflexivity.
      * rewrite N11, E33. reflexivity.
      * rewrite N12. reflexivity.
      * rewrite N13. reflexivity.
      * rewrite N14, U9. reflexivity.
      * rewrite N15, E32. unfold w64. f_equal. lia.
      * rewrite N16, E33. reflexivity.
      * rewrite N19, E32. unfold w64. f_equal. lia.
      * exact KR.
      * rewrite N18, EH70. reflexivity.
    + rewrite branch_ltu_U, (U_atom_off E 32 _ (-1) E32), U_lit in Hc0 by lia.
      apply Z.ltb_ge in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK lxo_Bspan AX_order.
      { xo_awr U9. }
      rename HFr into HFr3, HG0 into HG3. clear HF.
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
          aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a)
        by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr3 a Ha) by (xo_nowr U9 Hna);
            exact (K2 a Ha Hna)).
      assert (P3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
        by (intros a Hp; exact (lxo_pres_grows W _ _ a HG3 (P2 a Hp))).
      clear HFr3 HG3.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      assert (SVA : val_mem segs (arm W (ms_mem ms1)) (lf_F cx + AX_AT) 8 0).
      { unfold AX_AT.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 208 8%N (SLit 0) 0 RG0) end.
        - exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ XO_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
      prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14. prreg HS (15%bv : bv 5) N15.
      prreg HS (16%bv : bv 5) N16. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
      pmkst HS.
      apply JOIN.
      * exact HJ.
      * exact K3.
      * exact P3.
      * exact SVA.
      * lia.
      * rewrite N10, E33. reflexivity.
      * rewrite N11, E33. reflexivity.
      * rewrite N12. reflexivity.
      * rewrite N13. reflexivity.
      * rewrite N14, U9. reflexivity.
      * rewrite N15. unfold w64. f_equal. lia.
      * rewrite N16, E33. reflexivity.
      * rewrite N19. unfold w64. f_equal. lia.
      * exact KR.
      * rewrite N18, EH70. reflexivity.
Qed.

End lx.
