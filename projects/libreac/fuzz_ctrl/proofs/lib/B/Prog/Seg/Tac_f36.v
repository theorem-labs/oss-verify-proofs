(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 1754 of its 1873 lines of code are new or changed and 892 lines of the source are left out. *)
(* Helpers of segment F36 (lib/B/Prog/Seg/F36.v) of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B): the pure
   byte-list / shadow / side-stack arithmetic, the FRA readers (frame place, sp facts, heap-block apartness), the
   side-stack premises of the reac_box_catalogue_match call (f36_fp_call), the FRA moves across that call
   (f36_fra_run) and across a shadow store of the frame (f36_fra_meta), and the call's machine run (f36_evt_call,
   by the callee's lib/B contract, a premise). rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag RcMatch RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  asan_stack_malloc_c reac_box_catalogue_match_c reac_ctrl_parse_c reac_ctrl_classify_box_frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Import ListNotations.
Module BYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Import BYK.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

Local Definition BCMP : Z := 0x98930.
Local Definition REAL_BCMP : Z := 0xa2610.
Local Definition REAL_MEMCMP : Z := 0xa2608.
Local Definition MEMCMP : Z := 0x98a00.

(* ===================== pure helpers ===================== *)

(* A one-byte store of a register writes its low byte. *)
Lemma f36_le1_byte : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma f36_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* n bytes that are all present form a list. *)
Lemma f36_ba_present : forall m n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat i)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  intros m n. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [exact Ha|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b0 & Hb0).
    assert (Hrest : forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + 1 + Z.of_nat i)) = Some b).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as (b & Hb). exists b.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact Hb. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrest) as (bs & (Ha' & Hl' & Hb') & Hlen).
    exists (b0 :: bs). split; [|cbn [length]; lia].
    split; [exact Ha|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. exact Hb0.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hb'. cbn [length] in Hi. lia.
Qed.

(* A present byte of a list read at its address. *)
Lemma f36_ba_some : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa (a + i)) = Some b.
Proof.
  intros m a bs i (_ & _ & H) Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma f36_sh_frame_of : forall fr k, 0 <= fr -> fr mod 8 = 0 -> 0 <= k ->
  shadow_addr (fr + 8 * k) = shadow_addr fr + k.
Proof. unfold shadow_addr. intros fr k H0 H8 Hk. Z.div_mod_to_equations. lia. Qed.

Lemma f36_sh_frame : forall fr y k, 0 <= fr -> fr mod 8 = 0 -> 0 <= y -> shadow_addr y = shadow_addr fr + k ->
  fr + 8 * k <= y < fr + 8 * k + 8.
Proof. unfold shadow_addr. intros fr y k H0 H8 Hy E. Z.div_mod_to_equations. lia. Qed.

Lemma f36_sh_mono : forall y z, y <= z -> shadow_addr y <= shadow_addr z.
Proof. intros y z H. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* Below an 8-aligned bound, the shadow byte is below the bound's shadow byte. *)
Lemma f36_sh_lt : forall y z, z mod 8 = 0 -> y < z -> shadow_addr y < shadow_addr z.
Proof. intros y z H8 H. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma f36_in_shadow_bnd : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

(* addressable survives writes apart from the shadow bytes of its range. *)
Lemma f36_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

(* KNT (SlotInv, adopt 11: the kind-name table's 112 bytes at KNC.KIND_NAME = 0x9f580 (v1.9.0), image data below GT,
   and their addressability) survives writes apart from the table's bytes and their shadow bytes. *)
Lemma f36_knt_keep : forall W m m', KNT m -> munch W m m' ->
  (forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 -> outside W x /\ outside W (shadow_addr x)) -> KNT m'.
Proof.
  intros W m m' (Hb & Had) MU HW.
  assert (HL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
  split.
  - apply (fl_bytes W m m' KNC.KIND_NAME KNC.kind_name_bytes Hb MU).
    rewrite HL. intros x Hx. refine (proj1 (HW x _)). lia.
  - apply (f36_addr_keep W m m' _ 112 Had MU). intros i Hi. refine (proj2 (HW _ _)). lia.
Qed.

(* A range addressable byte by byte is addressable. *)
Lemma f36_addr_bytes : forall m lo n, 0 <= lo -> 0 <= n -> lo + n <= APPMEM_END ->
  (forall a, lo <= a < lo + n -> addressable m a 1) -> addressable m lo n.
Proof.
  intros m lo n Hlo Hn Hend H.
  split; [exact Hlo|]. split; [exact Hn|]. split; [exact Hend|].
  intros i Hi. destruct (H (lo + i) ltac:(lia)) as (_ & _ & _ & HA).
  pose proof (HA 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0.
Qed.

Lemma f36_rg_mod : forall regs r a b, rg regs r a -> rg regs r b -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof.
  unfold rg. intros regs r a b Ha Hb. rewrite Ha in Hb. apply (f_equal bv_unsigned) in Hb.
  rewrite !Z_to_bv_unsigned in Hb. exact Hb.
Qed.

(* Two in-range values of one register are the same value. *)
Lemma f36_reg_eq : forall (regs : bvmap 5 word) (r : bv 5) a b,
  getr regs r = Z_to_bv 64 a -> getr regs r = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb Ra Rb.
  assert (E : Z_to_bv 64 a = Z_to_bv 64 b) by congruence.
  apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

(* A readable-and-writable stack window survives a run that keeps every byte of it backed. *)
Lemma f36_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
  rewrite wa_unsigned by lia. exact Ho.
Qed.

(* A value of s1 within 416 bytes of the spill base A (both read through rg) is A. *)
Lemma f36_rg_near : forall (regs : bvmap 5 word) (r : bv 5) a b, rg regs r a -> rg regs r b ->
  416 <= a -> a + 416 <= 2 ^ 64 -> -400 <= b -> b + 8 <= 2 ^ 64 -> b = a.
Proof.
  intros regs r a b Ha Hb H1 H2 H3 H4.
  pose proof (f36_rg_mod regs r b a Hb Ha) as E. rewrite (Z.mod_small a) in E by lia.
  pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)) as D. rewrite E in D. lia.
Qed.

(* The thread-pointer word read in m' is the one of m when the run kept its 8 bytes. *)
Lemma f36_word_mem_back : forall W m m' a v, munch W m m' ->
  (forall x, a <= x < a + 8 -> outside W (bv_unsigned (Z_to_bv 64 x))) ->
  word_mem rsegs m' a v -> word_mem rsegs m a v.
Proof.
  intros W m m' a v MU HW H k Hk. rewrite <- (H k Hk). unfold mbyte.
  rewrite (MU (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|]. apply HW. lia.
Qed.

(* The side stack's metadata cells lie in its first 36864 bytes. *)
Lemma f36_fs_meta_ge : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [[c [Hc Hr]] | [c [jj [Hc [Hj Heq]]]]]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. pose proof (a_fs_flag_range FS c jj Hc Hj). lia.
Qed.


(* The registered globals (AF.frame_AG) lie below 657928 (v1.9.0's frame_AG ends at 0xa0708 = 657160; checked by
   computation). *)
Lemma f36_ag_bound : forall a, in_globals AF.frame_AG a -> 0 <= a < 657928.
Proof.
  intros a (lo & len & Hil & Hr).
  assert (HB : forallb (fun p => andb (0 <=? fst p) (fst p + snd p <? 657928)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB.
  pose proof (HB (lo, len) Hil) as H. cbn [fst snd] in H.
  apply andb_prop in H as (H1 & H2). apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* The catalogue is one registered global and lies in the image's RELRO range. *)
Lemma f36_cat_AG : In (0x9f620, 3256) AF.frame_AG.
Proof. apply (nth_error_In _ 55%nat). vm_compute. reflexivity. Qed.

Lemma f36_cat_RELRO : In (0x9f168, 9344) AF.frame_RELRO.
Proof. unfold AF.frame_RELRO. cbn [In]. left. reflexivity. Qed.

(* A spilled word at s1 + off read at the FRA spill base A (the existential base of `spill` is A; both bases
   are compared through Z_to_bv 64, so the byte range of the cell pins the existential one). *)
Lemma f36_spill : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold rg in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal bv_unsigned) in HA'. rewrite !MState.unsigned_lit_wrap in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* A sub-range of an addressable range is addressable. *)
Lemma f36_addr_sub : forall m p n k n', addressable m p n -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  addressable m (p + k) n'.
Proof.
  intros m p n k n' (H0 & H1 & H2 & H) Hk Hn' Hkn.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros x Hx. replace (p + k + x) with (p + (k + x)) by lia. apply H. lia.
Qed.

(* A registered global of frame_AG is addressable over its whole length (AGc is per byte). *)
Lemma f36_ag_addr : forall (m : word -> option byte) lo len,
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  In (lo, len) AF.frame_AG -> 0 <= lo -> 0 <= len -> lo + len <= APPMEM_END ->
  addressable m lo len.
Proof.
  intros m lo len HAG Hin Hlo Hlen Hend.
  apply f36_addr_bytes; [exact Hlo | exact Hlen | exact Hend |].
  intros a Ha. apply HAG. exists lo, len. split; [exact Hin | lia].
Qed.

Lemma f36_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* A branch arm the facts in context exclude. *)
Ltac f36_bad HC :=
  exfalso;
  first [ congruence
        | discriminate HC
        | (rewrite ?f36_eqb_lit in HC by lia; cbn [negb] in HC;
           first [ (apply Bool.negb_true_iff in HC; apply Z.eqb_neq in HC; lia)
                 | (apply Bool.negb_false_iff in HC; apply Z.eqb_eq in HC; lia)
                 | (apply Z.eqb_eq in HC; lia) | (apply Z.eqb_neq in HC; lia) ])
        | (vm_compute in HC; discriminate HC) ].
Ltac f36_nt := let H := fresh "HC" in first [ if_cases H; [f36_bad H | clear H] | idtac ].
Ltac f36_tk := let H := fresh "HC" in first [ if_cases H; [clear H | f36_bad H] | idtac ].

(* ===================== model facts of turn j ===================== *)

Lemma f36_bz_range : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma f36_fL_nonneg : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb.
  pose proof (f36_bz_range (nthb inp (Z.to_nat c))). pose proof (f36_bz_range (nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma f36_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fc]. unfold c0, nlen. lia.
  - change (fc inp (S j)) with (f_next inp (fc inp j)). pose proof (f36_fL_nonneg inp (fc inp j)).
    unfold f_next, f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma f36_t_facts : forall inp j,
  0 <= t_c inp j <= nlen inp /\ t_left inp j = nlen inp - t_c inp j /\
  0 <= t_h inp j <= t_left inp j /\ 0 <= t_len inp j <= t_left inp j - t_h inp j /\
  t_body inp j = t_c inp j + t_h inp j.
Proof.
  intros inp j. pose proof (f36_fc_range inp j) as R. pose proof (f36_fL_nonneg inp (fc inp j)) as L.
  unfold t_c, t_left, t_h, t_len, t_body. unfold f_body, f_len, f_h, f_left in *. lia.
Qed.

Lemma f36_len_nonneg : forall inp j, 0 <= t_len inp j.
Proof. intros inp j. pose proof (f36_t_facts inp j) as (_ & _ & _ & (H & _) & _). exact H. Qed.

Lemma f36_phi_length : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (f36_t_facts inp j) as (R & EL & (H1 & H2) & (H3 & H4) & EB).
  unfold t_phi, f_phi. rewrite length_firstn, length_skipn.
  change (f_len inp (fc inp j)) with (t_len inp j). change (f_body inp (fc inp j)) with (t_body inp j).
  unfold nlen in *. lia.
Qed.

Lemma f36_phi_lenZ : forall inp j, Z.of_nat (length (t_phi inp j)) = t_len inp j.
Proof. intros inp j. rewrite f36_phi_length. apply Z2Nat.id. apply f36_len_nonneg. Qed.

Lemma f36_fr50_firstn : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold fr50. rewrite firstn_app.
  replace (50 - length bs)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

(* With len >= 50 the 50 bytes t_g of turn j are the first 50 bytes of Phi. *)
Lemma f36_tg_bytes : forall m phi inp j, 50 <= t_len inp j -> bytes_at rsegs m phi (t_phi inp j) ->
  bytes_at rsegs m phi (t_g inp j).
Proof.
  intros m phi inp j H50 Hb. unfold t_g.
  rewrite f36_fr50_firstn by (rewrite f36_phi_length; lia).
  pose proof (f36_ba_sub m phi (t_phi inp j) 0 50 Hb ltac:(rewrite f36_phi_length; lia)) as Hs.
  rewrite Z.add_0_r, skipn_O in Hs. exact Hs.
Qed.

(* row_of_block: the first matching row, or 0. *)
Lemma f36_rob_hit : forall blk fuel k i, (k <= i < k + fuel)%nat ->
  (forall i', (k <= i' < i)%nat -> decl_i (Z.of_nat i') <> blk) -> decl_i (Z.of_nat i) = blk ->
  rob blk k fuel = CAT + CAT_ROW * Z.of_nat i.
Proof.
  intros blk fuel. induction fuel as [|f IH]; intros k i Hk Hprev Hi; [lia|].
  cbn [rob]. destruct (bool_decide (decl_i (Z.of_nat k) = blk)) eqn:E.
  - apply bool_decide_eq_true in E. destruct (Nat.eq_dec k i) as [->|Hne]; [reflexivity|].
    exfalso. apply (Hprev k); [lia | exact E].
  - apply bool_decide_eq_false in E. apply IH; [| intros i' Hi'; apply Hprev; lia | exact Hi].
    destruct (Nat.eq_dec k i) as [->|Hne]; [exfalso; apply E; exact Hi | lia].
Qed.

Lemma f36_rob_miss : forall blk fuel k, (forall i', (k <= i' < k + fuel)%nat -> decl_i (Z.of_nat i') <> blk) ->
  rob blk k fuel = 0.
Proof.
  intros blk fuel. induction fuel as [|f IH]; intros k H; [reflexivity|].
  cbn [rob]. destruct (bool_decide (decl_i (Z.of_nat k) = blk)) eqn:E.
  - apply bool_decide_eq_true in E. exfalso. exact (H k ltac:(lia) E).
  - apply IH. intros i' Hi'. apply H. lia.
Qed.

Lemma f36_want_m_hit : forall inp j i, t_rowsel inp j = true -> (i <= 10)%nat ->
  (forall i', (i' < i)%nat -> t_blk inp j <> decl_i (Z.of_nat i')) -> t_blk inp j = decl_i (Z.of_nat i) ->
  t_want_m inp j = CAT + CAT_ROW * Z.of_nat i.
Proof.
  intros inp j i Hsel Hi Hprev Hhit. unfold t_want_m, row_of_block. rewrite Hsel.
  apply f36_rob_hit; [lia | | symmetry; exact Hhit].
  intros i' Hi' E. apply (Hprev i'); [lia | symmetry; exact E].
Qed.

Lemma f36_want_m_miss : forall inp j, t_rowsel inp j = true ->
  (forall i', (i' < 11)%nat -> t_blk inp j <> decl_i (Z.of_nat i')) -> t_want_m inp j = 0.
Proof.
  intros inp j Hsel H. unfold t_want_m, row_of_block. rewrite Hsel.
  apply f36_rob_miss. intros i' Hi' E. apply (H i'); [lia | symmetry; exact E].
Qed.

Lemma f36_want_m_unsel : forall inp j, t_rowsel inp j = false -> t_want_m inp j = 0.
Proof. intros inp j H. unfold t_want_m. rewrite H. reflexivity. Qed.

Definition f36_W (S FS : Z) : list ivl :=
  [(S - CM_K, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - CM_K), shadow_addr S)].

(* ===================== more pure helpers (byte lists, disjointness) ===================== *)

(* A run of bytes that are all present and all satisfy P is a bytes_at of such a list. *)
Lemma f36_bytes_PN : forall (P : byte -> Prop) m a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = k /\ Forall P bs.
Proof.
  intros P m a k. revert a. induction k as [|k IH]; intros a H0 H1 H.
  - exists []. split; [|split; [reflexivity | constructor]].
    split; [exact H0|]. split; [cbn [length]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - destruct (H 0 ltac:(lia)) as (b & Hb & HPb). rewrite Z.add_0_r in Hb.
    assert (Hrec : forall i, 0 <= i < Z.of_nat k -> exists b', mbyte rsegs m (a + 1 + i) = Some b' /\ P b').
    { intros i Hi. destruct (H (1 + i) ltac:(lia)) as (b' & Hb' & HP'). exists b'.
      split; [|exact HP']. replace (a + 1 + i) with (a + (1 + i)) by lia. exact Hb'. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrec) as (bs & Hbs & Hlen & HPbs).
    exists (b :: bs). split; [|split; [cbn [length]; lia | constructor; assumption]].
    destruct Hbs as (_ & _ & Hnth).
    split; [exact H0|]. split; [cbn [length]; rewrite Hlen; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hnth. cbn [length] in Hi. lia.
Qed.

Lemma f36_bytes_P : forall (P : byte -> Prop) m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ Z.of_nat (length bs) = n /\ Forall P bs.
Proof.
  intros P m a n H0 Hn H1 H.
  destruct (f36_bytes_PN P m a (Z.to_nat n) H0 ltac:(rewrite Z2Nat.id by lia; lia)
              ltac:(rewrite Z2Nat.id by lia; exact H)) as (bs & Hbs & Hlen & HP).
  exists bs. split; [exact Hbs|]. split; [rewrite Hlen, Z2Nat.id by lia; reflexivity | exact HP].
Qed.

Lemma f36_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with (bytes_le_to_Z bs mod 2^64).
  rewrite (Z_to_le_bytes_mod 8 _ 64) by lia. rewrite <- L. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

(* Eight present bytes read as some word. *)
Lemma f36_word_present : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b) ->
  exists w : word, bytes_at rsegs m a (le8 w).
Proof.
  intros m a H0 H1 H.
  assert (HP : forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b /\ True).
  { intros i Hi. destruct (H i Hi) as (b & Hb). exists b. split; [exact Hb | exact I]. }
  destruct (f36_bytes_P (fun _ => True) m a 8 H0 ltac:(lia) H1 HP) as (bs & Hbs & Hlen & _).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite f36_le8_of_bytes by lia. exact Hbs.
Qed.

(* A word cell determines its value. *)
Lemma f36_wm_uniq : forall mem a v1 v2, word_mem rsegs mem a v1 -> word_mem rsegs mem a v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros mem a v1 v2 H1 H2 R1 R2.
  assert (D : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2. rewrite E1 in E2.
    injection E2 as E2.
    pose proof (kb_byte_unsigned v1 8 k) as K1. pose proof (kb_byte_unsigned v2 8 k) as K2.
    unfold bv_unsigned in K1, K2. rewrite K1, K2 in E2. exact E2. }
  pose proof (kb_le8_digits v1 R1) as G1. pose proof (kb_le8_digits v2 R2) as G2.
  rewrite (D 0%nat ltac:(lia)), (D 1%nat ltac:(lia)), (D 2%nat ltac:(lia)), (D 3%nat ltac:(lia)),
          (D 4%nat ltac:(lia)), (D 5%nat ltac:(lia)), (D 6%nat ltac:(lia)), (D 7%nat ltac:(lia)) in G1.
  lia.
Qed.

(* Two nonempty ranges are apart when a predicate holds on every byte of one and on no byte of the other. *)
Lemma f36_dj_pt : forall (Q : Z -> Prop) a b c d, a < b -> c < d ->
  (forall x, a <= x < b -> Q x) -> (forall x, c <= x < d -> ~ Q x) -> RcLay.ly_dj a b c d.
Proof.
  intros Q a b c d Hab Hcd HQ HnQ. unfold RcLay.ly_dj.
  destruct (Z_le_gt_dec b c) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec d a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (HnQ (Z.max a c) ltac:(lia)). apply HQ. lia.
Qed.

Lemma f36_sh_lo : forall a, 0 <= a -> LOWMEM_END <= shadow_addr a.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, LOWMEM_END.
  assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
Qed.

Lemma f36_sh_hi : forall a, a <= APPMEM_END -> shadow_addr a <= HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; unfold APPMEM_END in *; lia).
  lia.
Qed.

(* The twelve side-stack ranges of the classes 0, 1, 2 in numbers (fs_B c = 64 * 2^c, fs_M c = 2^(14-c)). *)
Lemma f36_fs_ranges : forall FS,
  fs_hint FS 0 = FS /\ fs_hint FS 1 = FS + 8 /\ fs_hint FS 2 = FS + 16 /\
  fs_flag FS 0 0 = FS + 4096 /\ fs_flag FS 1 0 = FS + 20480 /\ fs_flag FS 2 0 = FS + 28672 /\
  fs_M 0 = 16384 /\ fs_M 1 = 8192 /\ fs_M 2 = 4096 /\
  fs_frame FS 0 0 = FS + 36864 /\ fs_frame FS 0 (fs_M 0) = FS + 1085440 /\
  fs_frame FS 1 0 = FS + 1085440 /\ fs_frame FS 1 (fs_M 1) = FS + 2134016 /\
  fs_frame FS 2 0 = FS + 2134016 /\ fs_frame FS 2 (fs_M 2) = FS + 3182592.
Proof.
  intros FS. unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  repeat split; first [ reflexivity | lia | (vm_compute (2 ^ 15) in *; lia) ].
Qed.

Lemma f36_W_eq : forall S FS, f36_W S FS =
  [(S - CM_K, S);
   (FS, FS + 8); (FS + 4096, FS + 20480); (FS + 36864, FS + 1085440);
   (shadow_addr (FS + 36864), shadow_addr (FS + 1085440));
   (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016));
   (FS + 16, FS + 24); (FS + 28672, FS + 32768); (FS + 2134016, FS + 3182592);
   (shadow_addr (FS + 2134016), shadow_addr (FS + 3182592));
   (shadow_addr (S - CM_K), shadow_addr S)].
Proof.
  intros S FS. destruct (f36_fs_ranges FS) as
    (H0 & H1 & H2 & H3 & H4 & H5 & M0 & M1 & M2 & F0 & F0' & F1 & F1' & F2 & F2').
  unfold f36_W, fp_w, fp_w1. cbn [flat_map app].
  rewrite H0, H1, H2, H3, H4, H5, F0, F0', F1, F1', F2, F2', M0, M1, M2.
  replace (FS + 4096 + 16384) with (FS + 20480) by lia.
  replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  replace (FS + 28672 + 4096) with (FS + 32768) by lia.
  replace (FS + 8 + 8) with (FS + 16) by lia.
  replace (FS + 16 + 8) with (FS + 24) by lia.
  reflexivity.
Qed.

(* A contiguous app range lies wholly in the low or wholly in the high app memory. *)
Lemma f36_app_split : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> app_mem a) ->
  hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo.
Proof.
  intros lo hi Hlt H. destruct (Z_le_gt_dec hi LOWMEM_END) as [L|L]; [left; exact L|right].
  destruct (Z_le_gt_dec LOWMEM_END lo) as [L2|L2].
  - pose proof (H lo ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - pose proof (H LOWMEM_END ltac:(lia)) as H3.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* The shadow bytes of a contiguous app range are shadow memory. *)
Lemma f36_shadow_ivl : forall lo hi x, (forall a, lo <= a < hi -> app_mem a) -> lo < hi ->
  shadow_addr lo <= x < shadow_addr hi -> in_shadow x.
Proof.
  intros lo hi x Happ Hlt Hx. unfold shadow_addr, ASAN_K in Hx.
  assert (Hlo : 0 <= lo)
    by (pose proof (Happ lo ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (Hhi : hi <= APPMEM_END)
    by (pose proof (Happ (hi - 1) ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  unfold in_shadow. destruct (f36_app_split lo hi Hlt Happ) as [HL|HH].
  - left. unfold ASAN_K, LOWMEM_END, LOWSHADOW_END in *. Z.div_mod_to_equations. lia.
  - right. unfold ASAN_K, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* An app byte outside the callee's window and outside the three metadata/frame bands of the classes 0, 1, 2 is
   outside the call's writes. *)
Lemma f36_out_app : forall S FS x,
  0 <= FS -> FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END ->
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - CM_K <= a < S -> app_mem a) ->
  app_mem x -> ~ (S - CM_K <= x < S) ->
  ~ (FS <= x < FS + 24) -> ~ (FS + 4096 <= x < FS + 32768) -> ~ (FS + 36864 <= x < FS + 3182592) ->
  outside (f36_W S FS) x.
Proof.
  intros S FS x HFS0 HFSS HSA HFSapp HWapp Hx Hw H1 H2 H3.
  assert (HK : 0 < CM_K) by (unfold CM_K; lia).
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  rewrite f36_W_eq. cbn [outside].
  repeat split; try (intros HC; lia).
  - intros HC. apply (app_not_shadow x Hx).
    apply (f36_shadow_ivl (FS + 36864) (FS + 1085440) x);
      [intros a Ha; apply HFSapp; lia | lia | exact HC].
  - intros HC. apply (app_not_shadow x Hx).
    apply (f36_shadow_ivl (FS + 1085440) (FS + 2134016) x);
      [intros a Ha; apply HFSapp; lia | lia | exact HC].
  - intros HC. apply (app_not_shadow x Hx).
    apply (f36_shadow_ivl (FS + 2134016) (FS + 3182592) x);
      [intros a Ha; apply HFSapp; lia | lia | exact HC].
  - intros HC. apply (app_not_shadow x Hx).
    apply (f36_shadow_ivl (S - CM_K) S x); [exact HWapp | lia | exact HC].
Qed.

(* The same for a byte at or above the callee's window: the side stack and every shadow byte are below it. *)
Lemma f36_out_hi : forall S FS x,
  0 <= FS -> FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END -> HIGHMEM_BEG <= S - CM_K -> S <= x ->
  outside (f36_W S FS) x.
Proof.
  intros S FS x HFS0 HFSS HSA HHI Hx.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HK : CM_K = 9136) by reflexivity.
  pose proof (f36_sh_hi S HSA) as HS1.
  pose proof (f36_sh_hi (FS + 3182592) ltac:(unfold HIGHMEM_BEG, APPMEM_END in *; lia)) as HS2.
  pose proof (f36_sh_mono (FS + 1085440) (FS + 3182592) ltac:(lia)) as HM1.
  pose proof (f36_sh_mono (FS + 2134016) (FS + 3182592) ltac:(lia)) as HM2.
  pose proof (f36_sh_mono (S - CM_K) S ltac:(lia)) as HM3.
  rewrite f36_W_eq. cbn [outside].
  repeat split; intros HC; unfold HIGHMEM_BEG in *; lia.
Qed.

(* The shadow byte of an application byte outside the side stack and outside the callee's window is outside the
   call's writes. *)
Lemma f36_out_sh_call : forall S FS x,
  0 <= FS -> FS mod 8 = 0 -> FS + FS_SIZE <= S - CM_K -> (S - CM_K) mod 8 = 0 -> S <= APPMEM_END ->
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - CM_K <= a < S -> app_mem a) ->
  app_mem x -> ~ (FS <= x < FS + 3182592) -> ~ (S - CM_K <= x < S) ->
  outside (f36_W S FS) (shadow_addr x).
Proof.
  intros S FS x HFS0 HFS8 HFSS HS8 HSA HFSapp HWapp Hx HnFS HnW.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HK : CM_K = 9136) by reflexivity.
  pose proof (shadow_of_app x Hx) as Hsh.
  assert (HAPPFS : forall lo hi, FS <= lo -> hi <= FS + FS_SIZE -> ~ (lo <= shadow_addr x < hi)).
  { intros lo hi Hlo Hhi HC. apply (app_not_shadow (shadow_addr x)); [|exact Hsh].
    apply HFSapp. lia. }
  rewrite f36_W_eq. cbn [outside].
  repeat split.
  - intros HC. apply (app_not_shadow (shadow_addr x)); [apply HWapp; lia | exact Hsh].
  - exact (HAPPFS FS (FS + 8) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 4096) (FS + 20480) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 36864) (FS + 1085440) ltac:(lia) ltac:(lia)).
  - intros HC. revert HC HnFS. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - exact (HAPPFS (FS + 8) (FS + 16) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 20480) (FS + 28672) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 1085440) (FS + 2134016) ltac:(lia) ltac:(lia)).
  - intros HC. revert HC HnFS. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - exact (HAPPFS (FS + 16) (FS + 24) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 28672) (FS + 32768) ltac:(lia) ltac:(lia)).
  - exact (HAPPFS (FS + 2134016) (FS + 3182592) ltac:(lia) ltac:(lia)).
  - intros HC. revert HC HnFS. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - intros HC. revert HC HnW. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
Qed.

Lemma f36_dj_lo : forall (W : list ivl) (c n : Z), (forall p, In p W -> c + n <= fst p) -> disjoint_from W c n.
Proof.
  induction W as [|[lo hi] W IH]; intros c n H; cbn [disjoint_from]; [exact I|].
  split.
  - left. pose proof (H (lo, hi) (or_introl eq_refl)) as Hp. cbn [fst] in Hp. lia.
  - apply IH. intros p Hp. apply H. right. exact Hp.
Qed.

Lemma f36_W_los : forall S FS p, 6283264 <= FS -> 6283264 <= S - CM_K -> In p (f36_W S FS) ->
  6283264 <= fst p.
Proof.
  intros S FS p HFS HS Hin.
  assert (HK : CM_K = 9136) by reflexivity.
  assert (HD1 : 0 <= (FS + 36864) / 8) by (apply Z.div_pos; lia).
  assert (HD2 : 0 <= (FS + 1085440) / 8) by (apply Z.div_pos; lia).
  assert (HD3 : 0 <= (FS + 2134016) / 8) by (apply Z.div_pos; lia).
  assert (HD4 : 0 <= (S - CM_K) / 8) by (apply Z.div_pos; lia).
  rewrite f36_W_eq in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]];
    subst p; cbn [fst]; unfold shadow_addr, ASAN_K in *; lia.
Qed.

(* A byte apart from the twelve side-stack ranges, from the window and from the window's shadow. *)
Lemma f36_out_dj : forall S FS x,
  ~ (S - CM_K <= x < S) -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  ~ (shadow_addr (S - CM_K) <= x < shadow_addr S) ->
  outside (f36_W S FS) x.
Proof.
  intros S FS x H1 H2 H3. unfold f36_W. cbn [app outside]. split; [exact H1|].
  apply fl_out_app; [exact H2|]. cbn [outside]. split; [exact H3 | exact I].
Qed.

(* The shadow bytes of a FRAME_BYTES-byte block apart from [b1, b2) are apart from the shadow of [b1, b2). *)
Lemma f36_sh_dj : forall a b1 b2 t, a mod 8 = 0 -> 0 <= a -> 0 <= b1 -> b1 <= b2 ->
  (a + FRAME_BYTES <= b1 \/ b2 <= a) ->
  shadow_addr a <= t < shadow_addr a + FRAME_SHADOW -> ~ (shadow_addr b1 <= t < shadow_addr b2).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros a b1 b2 t Ha8 Ha Hb1 Hb12 Hdj Ht HC. unfold shadow_addr, ASAN_K in *.
  destruct Hdj as [H|H]; Z.div_mod_to_equations; lia.
Qed.

(* ===================== the generated laws' inner lists, as this file reads them ===================== *)
(* AC.a_fs_ok (the side stack's runtime state, a_laws_fs_state's first clause) and AC.a_store_ok (the premise list
   of a_laws_fs_store) are taken apart or built here only, each by its statement. *)
Lemma f36_fs_ok_elim : forall m FS, AC.a_fs_ok m FS ->
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs m a /\ exists b, mbyte rsegs m a = Some b) /\
  word_mem rsegs m (FS + 88) 20 /\ mbyte rsegs m (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs m (AC.a_fs_hint FS c) h) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs m (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/
     mbyte rsegs m (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)).
Proof. intros m FS H. exact H. Qed.

Lemma f36_fs_ok_intro : forall m FS,
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs m a /\ exists b, mbyte rsegs m a = Some b) /\
  word_mem rsegs m (FS + 88) 20 /\ mbyte rsegs m (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs m (AC.a_fs_hint FS c) h) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs m (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/
     mbyte rsegs m (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)) ->
  AC.a_fs_ok m FS.
Proof. intros m FS H. exact H. Qed.

(* A real-stack byte may be stored to (a_store_ok's real-stack clause). *)
Lemma f36_store_ok_stk : forall H lo a, lo <= a < APPMEM_END -> AC.a_store_ok H lo a.
Proof. intros H lo a Ha. unfold AC.a_store_ok. tauto. Qed.

(* The shadow byte of a real-stack byte may be stored to (a_store_ok's shadow clause, real-stack case). *)
Lemma f36_store_ok_sh : forall H lo a b, a = shadow_addr b -> lo <= b < APPMEM_END -> AC.a_store_ok H lo a.
Proof.
  intros H lo a b E Hb. unfold AC.a_store_ok. right. right. right.
  exists b. split; [exact E | tauto].
Qed.

(* The side stack's state after the call: the hint word, flag bytes and frames of the classes 0, 1 and 2 come
   from the callee's fp at the return; the metadata of the other classes is unchanged, because the run writes only
   the class-0/1/2 bands, their shadow and the window. *)
Lemma f36_fs_ok : forall (m m' : word -> option byte) (S FS TP : Z) (W D : list ivl),
  AC.a_fs_ok m FS ->
  munch (f36_W S FS) m m' ->
  fp [0%nat; 1%nat; 2%nat] m' TP FS (S - CM_K) S W D ->
  FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END -> HIGHMEM_BEG <= S - CM_K ->
  AC.a_fs_ok m' FS.
Proof.
  intros m m' S FS TP W D HOK MU
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFSlo & HAwin & _ & _) HFSS HSA HHI.
  destruct HP as (HFS0 & HFSmod & HFSgt & HFSapp & HSTK).
  destruct (f36_fs_ok_elim m FS HOK) as (HOK1 & HOK2 & HOK3 & HOK4 & HOK5).
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HSZc : AC.FS_SIZE = 11571200) by reflexivity.
  pose proof (Forall_inv HCL) as HC0.
  pose proof (Forall_inv (Forall_inv_tail HCL)) as HC1.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCL))) as HC2.
  assert (HFSub : FS + FS_SIZE <= APPMEM_END).
  { pose proof (HFSapp (FS + FS_SIZE - 1) ltac:(lia)) as Hh.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HOUT : forall x, FS <= x < FS + FS_SIZE ->
            ~ (FS <= x < FS + 24) -> ~ (FS + 4096 <= x < FS + 32768) -> ~ (FS + 36864 <= x < FS + 3182592) ->
            outside (f36_W S FS) x).
  { intros x Hx G1 G2 G3.
    apply (f36_out_app S FS x ltac:(lia) HFSS HSA HFSapp HAwin (HFSapp x Hx) ltac:(lia) G1 G2 G3). }
  assert (MB : forall a, outside (f36_W S FS) a -> 0 <= a < 2 ^ 64 -> mbyte rsegs m' a = mbyte rsegs m a).
  { intros a Ho Ha. unfold mbyte. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact Ho. }
  assert (HB64 : FS + FS_SIZE <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  apply f36_fs_ok_intro. split; [|split; [|split; [|split]]].
  - intros a Ha. destruct HSTK as (_ & _ & HS).
    destruct (HS a ltac:(lia)) as [Hw (b & Hb)].
    split; [exact Hw | exists b; exact Hb].
  - pose proof (bytes_at_le8_word rsegs m' (FS + 88) (Z_to_bv 64 20) H88) as HW.
    rewrite MState.unsigned_lit in HW by lia. exact HW.
  - destruct H96 as (_ & _ & H96'). pose proof (H96' 0%nat ltac:(cbn; lia)) as HH.
    cbn [nth_error] in HH. rewrite Z.add_0_r in HH. exact HH.
  - intros c Hc.
    destruct (Nat.eq_dec c 0) as [->|Hne0].
    { destruct HC0 as (_ & h & flags & Hh & _). exists (bv_unsigned h).
      exact (bytes_at_le8_word rsegs m' (fs_hint FS 0) h Hh). }
    destruct (Nat.eq_dec c 1) as [->|Hne1].
    { destruct HC1 as (_ & h & flags & Hh & _). exists (bv_unsigned h).
      exact (bytes_at_le8_word rsegs m' (fs_hint FS 1) h Hh). }
    destruct (Nat.eq_dec c 2) as [->|Hne2].
    { destruct HC2 as (_ & h & flags & Hh & _). exists (bv_unsigned h).
      exact (bytes_at_le8_word rsegs m' (fs_hint FS 2) h Hh). }
    destruct (HOK4 c Hc) as (h & Hh). exists h.
    apply (word_mem_frame rsegs m m' _ _ Hh). intros kk Hk.
    assert (Hhint : AC.a_fs_hint FS c = FS + 8 * Z.of_nat c) by reflexivity.
    assert (Hc3 : 3 <= Z.of_nat c <= 10) by lia.
    apply MB; [rewrite Hhint; apply HOUT; lia | rewrite Hhint; lia].
  - intros c j Hc Hj.
    assert (Hfl : forall (cc : nat) (hh : word) (flags : list byte),
              bytes_at rsegs m' (fs_flag FS cc 0) flags -> Z.of_nat (length flags) = fs_M cc ->
              Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
              0 <= j < AC.a_fs_M cc ->
              mbyte rsegs m' (AC.a_fs_flag FS cc j) = Some (Z_to_bv 8 0) \/
              mbyte rsegs m' (AC.a_fs_flag FS cc j) = Some (Z_to_bv 8 1)).
    { intros cc hh flags Hfb Hfl' Hfb01 Hjj.
      assert (HM : AC.a_fs_M cc = fs_M cc) by reflexivity.
      rewrite HM in Hjj.
      destruct Hfb as (_ & _ & Hfb).
      assert (HjN : (Z.to_nat j < length flags)%nat) by lia.
      pose proof (Hfb (Z.to_nat j) HjN) as HH.
      destruct (nth_error flags (Z.to_nat j)) as [b|] eqn:E;
        [|exfalso; apply nth_error_None in E; lia].
      assert (Eaddr : fs_flag FS cc 0 + Z.of_nat (Z.to_nat j) = AC.a_fs_flag FS cc j)
        by (unfold fs_flag, AC.a_fs_flag; lia).
      rewrite Eaddr in HH.
      pose proof (proj1 (Forall_forall _ flags) Hfb01 b (nth_error_In _ _ E)) as Hb01.
      destruct Hb01 as [->| ->]; [left | right]; exact HH. }
    destruct (Nat.eq_dec c 0) as [->|Hne0].
    { destruct HC0 as (_ & h & flags & _ & Hfb & Hfl' & Hfb01). exact (Hfl 0%nat h flags Hfb Hfl' Hfb01 Hj). }
    destruct (Nat.eq_dec c 1) as [->|Hne1].
    { destruct HC1 as (_ & h & flags & _ & Hfb & Hfl' & Hfb01). exact (Hfl 1%nat h flags Hfb Hfl' Hfb01 Hj). }
    destruct (Nat.eq_dec c 2) as [->|Hne2].
    { destruct HC2 as (_ & h & flags & _ & Hfb & Hfl' & Hfb01). exact (Hfl 2%nat h flags Hfb Hfl' Hfb01 Hj). }
    assert (Hr : FS + 32768 <= AC.a_fs_flag FS c j < FS + 36864).
    { unfold AC.a_fs_flag. unfold AC.a_fs_M in Hj.
      destruct c as [|[|[|[|[|[|[|[|[|[|[|c]]]]]]]]]]];
        try (exfalso; revert Hc Hne0 Hne1 Hne2; clear; lia);
        cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj |- *;
        first [ lia | (vm_compute (2 ^ 15) in *; vm_compute in Hj; lia) ]. }
    destruct (HOK5 c j Hc Hj) as [HH|HH]; [left|right];
      (rewrite MB; [exact HH | apply HOUT; lia | lia]).
Qed.

(* Every segment of the image ends below 0x5fe000, so the callee's stack window has no ROM bytes. *)
Lemma f36_segs_below : BzBridge.seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f36_rom_none : forall a, 0 <= a < 2 ^ 64 -> 0x5fe000 <= a -> seg_rom rsegs (wa a) = None.
Proof.
  intros a Ha Hge. apply seg_rom_unmapped.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso.
  destruct (BzBridge.find_segment_below rsegs 0x5fe000 (bv_unsigned (wa a)) 1 s f36_segs_below E ltac:(lia))
    as [Hlt|Hn]; [|lia].
  rewrite Mem.wa_unsigned in Hlt by lia. lia.
Qed.

(* Each disjointness leaf names image constants, FS / frame / sp offsets and shadow endpoints. *)
Ltac f36_num :=
  cbv [RcLay.ly_dj TLS_INDEX REAL_TLS_GET_ADDR TSD_KEY_INITED TSD_KEY GOT_CF CF GOT_VERBOSITY VERBOSITY
       DTLS_TPOFF RT_TP RT_TSDMAIN RT_GT ASAN_GT AC.as_tp AC.ASYMS AC.GT AC.FS_SIZE FS_SIZE RT_FS_SIZE
       CM_K AF.SLOT_STACK HIGHMEM_BEG APPMEM_END LOWMEM_END LOWSHADOW_END HIGHSHADOW_BEG ASAN_K] in *; lia.
Ltac f36_dj_split := repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd].

(* ===================== IFS moves ===================== *)

(* IFS (the turn's two frame records at fr + 2688 / fr + 2768, 38 and 72 bytes by Tac_ro.tr_ID_length /
   tr_FG_length, and the local `first` [fr + 2880, fr + 2920)) moves to a memory that keeps the frame's bytes and the
   addressability of `first`. *)
Lemma f36_IFS_tr : forall g fr j regs regs' m m',
  IFS g fr j regs m ->
  (forall a bs, bytes_at rsegs m a bs -> fr <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
     bytes_at rsegs m' a bs) ->
  (addressable m (fr + 2880) 40 -> addressable m' (fr + 2880) 40) ->
  IFS g fr j regs' m'.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr j regs regs' m m' HI KF KA.
  pose proof HI as (_ & _ & _ & _ & _ & Hfst & _).
  apply (Tac_ro.ifs_keep g fr j regs regs' m m' HI).
  - intros Hb. apply KF; [exact Hb | lia | rewrite Tac_ro.tr_ID_length; cbn [Z.of_nat]; lia].
  - intros Hb. apply KF; [exact Hb | lia | rewrite Tac_ro.tr_FG_length; cbn [Z.of_nat]; lia].
  - intros a bs Ha Hab Hb. apply KF; [exact Hb | lia | lia].
  - exact (KA Hfst).
Qed.

(* FTURN (the cursor spills [A + 224] / [A + 232] and the frame's bytes at Phi) moves with the spills and the
   Phi bytes. *)
Lemma f36_FTURN_tr : forall g j phi regs regs' m m',
  FTURN g j phi regs m ->
  (forall off v, 0 <= off <= 336 -> spill regs m off v -> spill regs' m' off v) ->
  (bytes_at rsegs m phi (t_phi (g_in g) j) -> bytes_at rsegs m' phi (t_phi (g_in g) j)) ->
  FTURN g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' (H224 & H232 & Hb & Hl) KS KB.
  split; [apply KS; [lia | exact H224]|]. split; [apply KS; [lia | exact H232]|].
  split; [exact (KB Hb) | exact Hl].
Qed.

Section Tac_f36.
Context {fx : BYK.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Local Notation STKLO mem md := (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).

(* ---- the generated laws, as this file and F36.v read them (through SlotInv.LawFields where it has a lemma) ---- *)

(* a_laws_blocks (lw_blocks): a live block ends below stklo and in application memory, and each of its bytes is
   application memory off the side stack. lwb_byte's per-byte list is taken apart here only. *)
Lemma f36_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= STKLO mem md /\ end_in_app p n /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ _ Hend Hea Hall].
  split; [exact Hend|]. split; [exact Hea|].
  intros a Ha. pose proof (Hall a Ha) as Hb. decompose [and] Hb. split; assumption.
Qed.

(* a_laws_not_owned (lw_not_owned, its byte field): the runtime owns no side-stack byte and no real-stack byte. *)
Lemma f36_not_owned : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.a_in_fs AC.ASYMS mem a \/ STKLO mem md <= a < APPMEM_END) ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a.
Proof.
  intros H mem md a HAH Hor.
  exact (lwn_byte (lw_not_owned (APIf rc) H mem md a HAH ltac:(tauto))).
Qed.

(* a_laws_fs_store (no LawFields lemma), by its statement: a run that changes no byte outside a_store_ok, the side
   stack and the side stack's shadow, keeps writability and leaves the side stack a_fs_ok keeps AH, the owned set
   and the two stack bounds. *)
Lemma f36_fs_store : forall H mem mem' md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (STKLO mem md) a -> ~ (FS <= a < FS + AC.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  STKLO mem' md = STKLO mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md FS HAH Hw Hr P1 P2 P3.
  decompose [and] (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                     H mem mem' md FS HAH Hw Hr P1 P2 P3).
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* The Lib-evt -> SR bridge (F29's sl_run_lib). *)
Lemma f36_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* The frame's place (plan FP.1/FP.2), as in F29. *)
Lemma f36_fra_loc : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists FS, (exists w : word, bytes_at rsegs mem RT_TP (le8 w) /\ bv_unsigned w = FS) /\
    AC.GT <= FS /\ FS + AC.FS_SIZE <= STKLO mem md /\ (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    HIGHMEM_BEG <= STKLO mem md /\
    0 <= fr /\ AC.GT <= fr /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\
    ((STKLO mem md <= fr /\ fr + FRAME_BYTES <= APPMEM_END) \/ (FS <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE)).
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr hb regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof Hwin as (Hw0 & Hw1 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FSw & HFSw & HFok) & _).
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw)).
  { change (AC.as_tp AC.ASYMS) with RT_TP. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  destruct (lw_fs_place (APIf rc) _ mem md (bv_unsigned FSw) HAH Hwm HFSr) as [HGT HFSlo _ HFSapp].
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  assert (Rsp : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; unfold AC.aspZ; apply u64_range).
  pose proof Hhdr1 as (Hfr0 & Hfr8 & _). rewrite length_le8 in Hfr8. change (Z.of_nat 8) with 8 in Hfr8.
  exists (bv_unsigned FSw).
  split; [exists FSw; split; [exact HFSw | reflexivity]|].
  split; [exact HGT|]. split; [exact HFSlo|]. split; [exact HFSapp|]. split; [exact Hhi|].
  split; [exact Hfr0|].
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal fr ltac:(lia)) as R1. pose proof (Hreal (fr + FRAME_BYTES - 1) ltac:(lia)) as R2.
    split; [unfold AC.GT, HIGHMEM_BEG in *; lia|].
    split; [intros a Ha; pose proof (Hreal a Ha); unfold app_mem; right; lia|].
    left. lia.
  - assert (HFS1 : bv_unsigned FSw + AC.FS_SIZE <= 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
    assert (Hin : forall a, fr <= a < fr + FRAME_BYTES -> bv_unsigned FSw <= a < bv_unsigned FSw + AC.FS_SIZE).
    { intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hb & Hab).
      change (AC.as_tp AC.ASYMS) with RT_TP in Hb.
      pose proof (f36_wm_uniq mem RT_TP b (bv_unsigned FSw) Hb Hwm Hbr HFSr) as E. lia. }
    pose proof (Hin fr ltac:(lia)) as F1. pose proof (Hin (fr + FRAME_BYTES - 1) ltac:(lia)) as F2.
    split; [lia|].
    split; [intros a Ha; apply HFSapp; apply Hin; exact Ha|].
    right. lia.
Qed.

(* A byte of a live heap block is not a frame byte. *)
Lemma f36_fra_blk : forall g fr hb regs mem md p n a, FRA B APIf ra g fr hb regs mem md ->
  In (p, n) (hb ++ g_H g) -> p <= a < p + n -> fr <= a < fr + FRAME_BYTES -> False.
Proof.
  intros g fr hb regs mem md p n a HFRA Hin Ha Hfa.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  destruct (f36_blocks _ mem md p n HAH Hin) as (Hend & _ & Hall).
  destruct (Hall a Ha) as (_ & Hnfs).
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal a Hfa). lia.
  - exact (Hnfs (Hfs a Hfa)).
Qed.

(* The sp facts the callee contract asks for. *)
Lemma f36_fra_sp : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  0 <= AC.aspZ regs < 2 ^ 64 /\ AC.aspZ regs mod 16 = 0 /\ AC.aspZ regs <= APPMEM_END /\
  HIGHMEM_BEG <= AC.aspZ regs - FN_STACK /\ stk rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs) /\
  (exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ AC.aspZ regs <= A /\ fr + FRAME_BYTES <= A /\ A + 448 <= g_S g).
Proof.
  intros g fr hb regs mem md HFRA.
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlo & Hstk).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
    (hb ++ g_H g) mem md ltac:(destruct HFRA as (A & sp & s5 & _ & HAH & _); exact HAH)) as Hhi.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  split; [unfold AC.aspZ; exact (u64_range (getr regs 2))|].
  split; [rewrite Haspz; exact Hspm|].
  split; [rewrite Haspz; lia|].
  split; [lia|].
  split; [exact Hstk|].
  exists A. split; [exact Hr9|]. split; [lia|]. split; [rewrite Haspz; lia|]. split; [exact Hfa | exact HA416].
Qed.


Definition BLK (g : ghost) (j : nat) (phi fr : Z) (m : word -> option byte) : Prop :=
  forall x, phi <= x < phi + AC.a_size (flen g j) ->
    app_mem x /\ ~ (fr <= x < fr + FRAME_BYTES) /\ ~ AC.a_in_fs AC.ASYMS m x.

Lemma f36_rowsel_big : forall inp j, t_rowsel inp j = true -> 50 <= t_len inp j.
Proof.
  intros inp j H. unfold t_rowsel in H. apply andb_prop in H as [H _]. apply andb_prop in H as [Hk _].
  apply Z.eqb_eq in Hk.
  destruct (Z_le_gt_dec 50 (t_len inp j)) as [Hle|Hgt]; [exact Hle|].
  exfalso. assert (K0 : t_k inp j = 0) by (unfold t_k; apply ctrlparse_none; intros (HC & _ & _); lia).
  rewrite K0 in Hk. discriminate.
Qed.

Lemma f36_rowsel_tbig : forall inp j, t_rowsel inp j = true -> t_big inp j = true.
Proof. intros inp j H. unfold t_big. apply Z.leb_le. exact (f36_rowsel_big inp j H). Qed.

(* BLK from FRA's extra block (Phi, a_size len) (the runtime serves len = 0 as one byte): every byte of
   [Phi, Phi + a_size len) is application memory, is not a frame byte (a_laws_blocks with the frame's placement)
   and is off the side stack (a_laws_blocks). *)
Lemma f36_blk_of : forall g j phi fr regs mem md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md -> BLK g j phi fr mem.
Proof.
  intros g j phi fr regs mem md HFRA x Hx.
  assert (Hin : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (apply in_or_app; left; left; reflexivity).
  pose proof HFRA as (A & sp & s5 & _ & HAH & _).
  destruct (f36_blocks _ mem md phi (AC.a_size (flen g j)) HAH Hin) as (_ & _ & Hall).
  destruct (Hall x Hx) as (Hap & Hnfs).
  split; [exact Hap|]. split; [|exact Hnfs].
  intros Hfr. exact (f36_fra_blk g fr _ regs mem md phi (AC.a_size (flen g j)) x HFRA Hin Hx Hfr).
Qed.

Lemma f36_fp_cls : forall mem FS c,
  (c <= 2)%nat -> 0 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b) ->
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)) ->
  fp_cls mem FS c.
Proof.
  intros mem FS c Hc HFS0 HFSb Hpres Hflag.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (HSZc : AC.FS_SIZE = 11571200) by reflexivity.
  destruct (f36_fs_ranges FS) as (Rh0 & Rh1 & Rh2 & Rf0 & Rf1 & Rf2 & RM0 & RM1 & RM2 & _).
  assert (HB : FS <= fs_hint FS c /\ fs_hint FS c + 8 <= FS + 4096 /\
               FS + 4096 <= fs_flag FS c 0 /\ fs_flag FS c 0 + fs_M c <= FS + 32768 /\ 0 <= fs_M c).
  { destruct c as [|[|[|c]]];
      [ rewrite Rh0, Rf0, RM0 | rewrite Rh1, Rf1, RM1 | rewrite Rh2, Rf2, RM2 | lia ]; lia. }
  destruct HB as (HB1 & HB2 & HB3 & HB4 & HB5).
  unfold fp_cls. split; [lia|].
  destruct (f36_word_present mem (fs_hint FS c) ltac:(lia) ltac:(lia)
              ltac:(intros i Hi;
                    destruct (Hpres (fs_hint FS c + i) ltac:(lia)) as (_ & bb & Hbb);
                    exists bb; exact Hbb)) as (h & Hh).
  destruct (f36_bytes_P (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) mem (fs_flag FS c 0) (fs_M c)
              ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(intros i Hi;
                    pose proof (Hflag c i ltac:(lia) ltac:(change (AC.a_fs_M c) with (fs_M c); lia)) as Hf;
                    replace (AC.a_fs_flag FS c i) with (fs_flag FS c 0 + i) in Hf
                      by (unfold AC.a_fs_flag, fs_flag; lia);
                    destruct Hf as [Hf|Hf]; [exists (Z_to_bv 8 0) | exists (Z_to_bv 8 1)];
                      (split; [exact Hf | first [left; reflexivity | right; reflexivity]])))
    as (flags & Hfl & Hfllen & Hflb).
  exists h, flags. split; [exact Hh|]. split; [exact Hfl|]. split; [exact Hfllen | exact Hflb].
Qed.

(* The side-stack premises of reac_box_catalogue_match_contract (fp for the classes 0, 1, 2 and the thread cells
   apart from them) at a state with FRA: the base word at tp and its placement come from the runtime's cells
   (asan_fs_cells) and the heap laws a_laws_fs_place / a_laws_fs_state, the thread record from a_laws_thread, and
   the control-flag / verbosity / TLS cells from RT.  The caller's data range (the 50 bytes at Phi) is apart from
   the side stack because a live block is never a side-stack byte (a_laws_blocks). *)
Lemma f36_fp_call : forall g fr hb regs mem md phi len,
  FRA B APIf ra g fr hb regs mem md ->
  (50 <= len -> In (phi, len) (hb ++ g_H g)) ->
  exists FS,
    word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\ FS mod 4096 = 0 /\
    AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aspZ regs - CM_K /\
    (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    fp [0%nat; 1%nat; 2%nat] mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - CM_K) (AC.aspZ regs)
      (reac_box_catalogue_match_W (AC.aspZ regs)) (reac_box_catalogue_match_D phi len) /\
    reac_box_catalogue_match_tls mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - CM_K) (AC.aspZ regs).
Proof.
  intros g fr hb regs mem md phi len HFRA Hblk.
  destruct (f36_fra_sp g fr hb regs mem md HFRA)
    as (Hsp64 & Hspm & HspA & HspH & Hstkw & (A & Hr9 & HA64 & HspAle & HfrA & HA416)).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm' & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416' & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  rewrite Haspz in Hsp64, Hspm, HspA, HspH, Hstkw, HspAle |- *.
  assert (ETP : AC.as_tp AC.ASYMS = RT_TP) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HCMK : CM_K = 9136) by reflexivity.
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HSZ' : FS_SIZE = 11571200) by reflexivity.
  (* ---- the side stack's base and its placement ---- *)
  destruct (RT_fs_cells _ _ _ HRT)
    as (Htlsidx & Hdtpoff & Hdt & Hdt8 & (FSw & HFSb & HFSok) & (DBw & HDBb & HDBnz & HDBapp)).
  remember (bv_unsigned FSw) as FS eqn:EFS.
  assert (HFS64 : 0 <= FS < 2 ^ 64) by (rewrite EFS; apply u64_range).
  assert (HFSwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { rewrite ETP, EFS. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSb). }
  destruct HFSok as (HFSpos & HFSalign & HFSgt & HFSapp0).
  destruct (lw_fs_place (APIf rc) _ mem md FS HAH HFSwm HFS64) as [HGTFS HFShi HFSmod HFSapp].
  destruct (fsf_fs_state_fields (APIf rc) _ mem md FS HAH HFSwm HFS64)
    as (DBz & [HFSok' HDBzw HDBzr HDBznz HDBztp HDBzp HT48app]).
  destruct (f36_fs_ok_elim mem FS HFSok') as (HFSpres & HFS88 & HFS96 & HFShint & HFSflag).
  assert (NFSW : FS + AC.FS_SIZE <= sp - CM_K) by lia.
  assert (HFSub : FS + AC.FS_SIZE <= APPMEM_END).
  { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha. unfold APPMEM_END. lia. }
  assert (HWapp : forall a, sp - CM_K <= a < sp -> app_mem a).
  { intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  (* ---- the thread record ---- *)
  destruct (fsf_thread_fields (APIf rc) _ mem md HAH) as (C0 & T0 & [_ HC0wm HT0wm HC0rng HT0rng HC152 HT48]).
  destruct (RT_uw_cells _ _ _ HRT) as (Htsdi & Htsdk & _ & Htp88 & (Cw & HCwb)).
  pose proof (bytes_at_le8_word rsegs mem RT_TSDMAIN Cw HCwb) as HCwm.
  assert (ECw : bv_unsigned Cw = C0)
    by (apply (f36_wm_uniq mem RT_TSDMAIN); [exact HCwm | exact HC0wm | apply u64_range | lia]).
  assert (HCapp : forall x, C0 + 152 <= x < C0 + 160 -> app_mem x).
  { intros x Hx. pose proof (proj2 (HC152 (x - (C0 + 152)) ltac:(lia))) as H.
    replace (C0 + 152 + (x - (C0 + 152))) with x in H by lia. exact H. }
  assert (HCpt : forall x, C0 + 152 <= x < C0 + 160 ->
            x < STKLO mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HC152 (x - (C0 + 152)) ltac:(lia)) as (Hown & Hap).
    replace (C0 + 152 + (x - (C0 + 152))) with x in Hown by lia.
    pose proof (HCapp x Hx) as Hax.
    split.
    - destruct (Z_lt_le_dec x (STKLO mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : STKLO mem md <= x < APPMEM_END) by (unfold APPMEM_END; lia).
      exact (f36_not_owned _ mem md x HAH (or_intror Hst) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x)
        by (exists FS; split; [exact HFS64 | split; [exact HFSwm | exact Hin]]).
      exact (f36_not_owned _ mem md x HAH (or_introl HFSin) Hown). }
  assert (HTapp : forall x, T0 + 48 <= x < T0 + 64 -> app_mem x).
  { intros x Hx.
    pose proof (HT48app C0 T0 HC0wm ltac:(lia) HT0wm ltac:(lia) (x - (T0 + 48)) ltac:(lia)) as H.
    replace (T0 + 48 + (x - (T0 + 48))) with x in H by lia. exact H. }
  assert (HTpt : forall x, T0 + 48 <= x < T0 + 64 ->
            x < STKLO mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HT48 (x - (T0 + 48)) ltac:(lia)) as (Hown & _).
    replace (T0 + 48 + (x - (T0 + 48))) with x in Hown by lia.
    pose proof (HTapp x Hx) as Hax.
    split.
    - destruct (Z_lt_le_dec x (STKLO mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : STKLO mem md <= x < APPMEM_END) by (unfold APPMEM_END; lia).
      exact (f36_not_owned _ mem md x HAH (or_intror Hst) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x)
        by (exists FS; split; [exact HFS64 | split; [exact HFSwm | exact Hin]]).
      exact (f36_not_owned _ mem md x HAH (or_introl HFSin) Hown). }
  assert (HTpres : forall i, 0 <= i < 16 -> exists b, mbyte rsegs mem (T0 + 48 + i) = Some b)
    by (intros i Hi; exact (proj2 (HT48 i Hi))).
  (* ---- the thread's DTLS record ---- *)
  assert (EDBw : bv_unsigned DBw = DBz).
  { pose proof (bytes_at_le8_word rsegs mem (RT_TP + 8) DBw HDBb) as HDBwm.
    apply (f36_wm_uniq mem (AC.as_tp AC.ASYMS + 8));
      [rewrite ETP; exact HDBwm | exact HDBzw | apply u64_range | lia]. }
  assert (HDBpt : forall x, DBz + 24 <= x < DBz + 32 ->
            app_mem x /\ x < STKLO mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HDBzp x Hx) as (H1 & H2 & H4).
    split; [exact H1|]. split; [exact H2|]. intros Hin. apply H4.
    exists FS. split; [exact HFS64 | split; [exact HFSwm | exact Hin]]. }
  assert (NC0 : C0 + 160 <= APPMEM_END).
  { pose proof (HCapp (C0 + 159) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NT0 : T0 + 64 <= APPMEM_END).
  { pose proof (HTapp (T0 + 63) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NDB0 : DBz + 32 <= APPMEM_END).
  { pose proof (proj1 (HDBpt (DBz + 31) ltac:(lia))) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NC : C0 + 160 <= STKLO mem md) by (pose proof (proj1 (HCpt (C0 + 159) ltac:(lia))); lia).
  assert (NT : T0 + 64 <= STKLO mem md) by (pose proof (proj1 (HTpt (T0 + 63) ltac:(lia))); lia).
  assert (NDB : DBz + 32 <= STKLO mem md)
    by (pose proof (proj1 (proj2 (HDBpt (DBz + 31) ltac:(lia)))); lia).
  assert (HDB24 : bytes_at rsegs mem (bv_unsigned DBw + 24) (le8 (Z_to_bv 64 (AC.as_tp AC.ASYMS)))).
  { rewrite EDBw.
    apply (word_mem_le8 rsegs mem (DBz + 24) (AC.as_tp AC.ASYMS) HDBztp);
      [rewrite ETP; unfold RT_TP; lia | lia | lia]. }
  (* ---- the thread cells ---- *)
  assert (EDTu : bv_unsigned (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) = AC.as_tp AC.ASYMS + 32)
    by (apply MState.unsigned_lit; rewrite ETP; unfold RT_TP; lia).
  assert (ETSu : bv_unsigned (Z_to_bv 64 RT_TSDMAIN) = RT_TSDMAIN)
    by (apply MState.unsigned_lit; unfold RT_TSDMAIN; lia).
  assert (ETu : bv_unsigned (Z_to_bv 64 T0) = T0) by (apply MState.unsigned_lit; lia).
  pose proof (word_mem_le8 rsegs mem (C0 + 152) T0 HT0wm ltac:(lia) ltac:(lia) ltac:(lia)) as HT0b.
  destruct (f36_word_present mem (T0 + 48) ltac:(lia) ltac:(lia)
              ltac:(intros i Hi; exact (HTpres i ltac:(lia)))) as (tb & Htb).
  assert (HTpres2 : forall i, 0 <= i < 8 -> exists b, mbyte rsegs mem (T0 + 56 + i) = Some b).
  { intros i Hi. replace (T0 + 56 + i) with (T0 + 48 + (8 + i)) by lia. exact (HTpres (8 + i) ltac:(lia)). }
  destruct (f36_word_present mem (T0 + 56) ltac:(lia) ltac:(lia) HTpres2) as (te & Hte).
  assert (HTBE : bytes_at rsegs mem (T0 + 48) (le8 tb ++ le8 te)).
  { apply (proj2 (bytes_at_app rsegs mem (T0 + 48) (le8 tb) (le8 te))).
    split; [exact Htb|]. rewrite length_le8.
    replace (T0 + 48 + Z.of_nat 8) with (T0 + 56) by lia. exact Hte. }
  destruct (RT_cf_cells _ _ _ HRT) as (Hcf1 & _ & _ & _ & _ & Hcf137 & _ & _).
  destruct (RT_opt_cells _ _ _ HRT) as (_ & _ & Hopt3 & Hopt4).
  pose proof (RT_real_cells _ _ _ HRT) as HREAL.
  assert (HTLS : asan_tls_cells mem (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                   (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0).
  { unfold asan_tls_cells. rewrite EDTu, ETSu, ETu, ECw, ETP.
    split; [unfold TLS_INDEX; exact Htlsidx|].
    split; [exact (real_cell_of mem REAL_TLS_GET_ADDR MUSL_TLS_GET_ADDR HREAL
                     ltac:(vm_compute; reflexivity))|].
    split; [exact Hdt|].
    split; [replace (RT_TP + 32 + 8) with (RT_TP + 40) by lia; exact Hdt8|].
    split; [unfold TSD_KEY_INITED; exact Htsdi|].
    split; [unfold TSD_KEY; lia|].
    split; [unfold TSD_KEY; exact Htsdk|].
    split; [exact Htp88|].
    split; [replace (RT_TSDMAIN + 8 * 0) with RT_TSDMAIN by lia; exact HCwb|].
    split; [exact HT0b|].
    split; [exists tb, te; exact HTBE|].
    split; [unfold GOT_CF; exact Hcf1|].
    split; [unfold CF; exact Hcf137|].
    split; [unfold GOT_VERBOSITY; exact Hopt3|].
    split; [unfold VERBOSITY; exact Hopt4|].
    split; [unfold DTLS_TPOFF; exact Hdtpoff|].
    split; [exact HDBb|].
    split; [rewrite EDBw; lia|].
    rewrite ETP in HDB24. exact HDB24. }
  (* ---- numeric facts for the disjointness leaves ---- *)
  assert (SB1 : LOWMEM_END <= shadow_addr (FS + 36864)) by (apply f36_sh_lo; lia).
  assert (SB2 : LOWMEM_END <= shadow_addr (FS + 1085440)) by (apply f36_sh_lo; lia).
  assert (SB3 : LOWMEM_END <= shadow_addr (FS + 2134016)) by (apply f36_sh_lo; lia).
  assert (SB4 : LOWMEM_END <= shadow_addr (FS + 3182592)) by (apply f36_sh_lo; lia).
  assert (SB5 : LOWMEM_END <= shadow_addr (sp - CM_K)) by (apply f36_sh_lo; lia).
  assert (SB6 : LOWMEM_END <= shadow_addr sp) by (apply f36_sh_lo; lia).
  assert (SH1 : shadow_addr (FS + 36864) <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (SH2 : shadow_addr (FS + 1085440) <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (SH3 : shadow_addr (FS + 2134016) <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (SH4 : shadow_addr (FS + 3182592) <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (SH5 : shadow_addr (sp - CM_K) <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (SH6 : shadow_addr sp <= HIGHMEM_BEG) by (apply f36_sh_hi; lia).
  assert (HGAP : forall x, LOWMEM_END <= x < HIGHMEM_BEG -> ~ app_mem x).
  { intros x Hx Hap. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (AS_C : RcLay.ly_dj (C0 + 152) (C0 + 160) LOWMEM_END HIGHMEM_BEG).
  { apply (f36_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HCapp | exact HGAP]. }
  assert (AS_T : RcLay.ly_dj (T0 + 48) (T0 + 64) LOWMEM_END HIGHMEM_BEG).
  { apply (f36_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HTapp | exact HGAP]. }
  assert (AS_DB : RcLay.ly_dj (DBz + 24) (DBz + 32) LOWMEM_END HIGHMEM_BEG).
  { apply (f36_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
    | intros x Hx; exact (proj1 (HDBpt x Hx)) | exact HGAP]. }
  assert (DJ_C_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (C0 + 152) (C0 + 160)).
  { apply (f36_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [lia | lia | intros x Hx; exact Hx | intros x Hx; exact (proj2 (HCpt x Hx))]. }
  assert (DJ_T_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (T0 + 48) (T0 + 64)).
  { apply (f36_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [lia | lia | intros x Hx; exact Hx | intros x Hx; exact (proj2 (HTpt x Hx))]. }
  assert (DJ_DB_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (DBz + 24) (DBz + 32)).
  { apply (f36_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [lia | lia | intros x Hx; exact Hx | intros x Hx; exact (proj2 (proj2 (HDBpt x Hx)))]. }
  (* ---- the goal ---- *)
  exists FS.
  split; [exact HFSwm|].
  split; [exact HFS64|].
  split; [exact HFSmod|].
  split; [exact HGTFS|].
  split; [exact NFSW|].
  split; [exact HFSapp|].
  split.
  { exists (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)), (Z_to_bv 64 RT_TSDMAIN), Cw, (Z_to_bv 64 T0), DBw, 0.
    split; [exact HTLS|].
    split; [rewrite ETP, EFS, MState.Z_to_bv_bv_unsigned; exact HFSb|].
    split.
    { unfold fs_place. split; [lia|]. split; [exact HFSmod|].
      split; [unfold ASAN_GT; unfold AC.GT in HGTFS; lia|].
      split; [intros a Ha; apply HFSapp; lia|].
      split; [lia|]. split; [lia|].
      intros a Ha. destruct (HFSpres a ltac:(lia)) as (Hw & b & Hb).
      split; [exact Hw | exists b; exact Hb]. }
    split; [exact (word_mem_le8 rsegs mem (FS + 88) 20 HFS88 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split.
    { split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. rewrite Z.add_0_r. exact HFS96. }
    split.
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
        apply (f36_fp_cls mem FS); solve [ lia | exact HFSpres | exact HFSflag ]. }
    split; [lia|].
    split; [exact HWapp|].
    split.
    { unfold reac_box_catalogue_match_W, fp_dj. cbn [fp_tls app].
      rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
      destruct (f36_fs_ranges FS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rfr0 & _). rewrite Rfr0.
      clear - HspH HspA HFS64 HGTFS NFSW HFSub NC NT NDB Hstklo HS4 HC0rng HT0rng HDBzr NC0 NT0 NDB0
        HSS HFN HCMK HSZ HSZ'.
      f36_dj_split; f36_num. }
    { unfold reac_box_catalogue_match_D.
      destruct (Z.ltb_spec0 len 50) as [Hlt|Hge]; [unfold fp_dj; apply Forall_nil|].
      assert (HPHI : forall x, phi <= x < phi + 50 -> app_mem x /\ ~ (FS <= x < FS + AC.FS_SIZE)).
      { intros x Hx.
        destruct (f36_blocks _ mem md phi len HAH (Hblk ltac:(lia))) as (_ & _ & Hb).
        destruct (Hb x ltac:(lia)) as (Hap & Hnfs).
        split; [exact Hap|]. intros Hin. apply Hnfs.
        exists FS. split; [exact HFS64 | split; [exact HFSwm | exact Hin]]. }
      assert (AS_PHI : RcLay.ly_dj phi (phi + 50) LOWMEM_END HIGHMEM_BEG).
      { apply (f36_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
        | intros x Hx; exact (proj1 (HPHI x Hx)) | exact HGAP]. }
      assert (DJ_PHI_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) phi (phi + 50)).
      { apply (f36_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
          [lia | lia | intros x Hx; exact Hx | intros x Hx; exact (proj2 (HPHI x Hx))]. }
      destruct (f36_fs_ranges FS) as
        (Rh0 & Rh1 & Rh2 & Rf0 & Rf1 & Rf2 & RM0 & RM1 & RM2 & Rfr0 & Rfr0' & Rfr1 & Rfr1' & Rfr2 & Rfr2').
      unfold fp_dj, fp_w, fp_w1. cbn [flat_map app].
      rewrite Rfr0, Rfr0', Rfr1, Rfr1', Rfr2, Rfr2', Rh0, Rh1, Rh2, Rf0, Rf1, Rf2, RM0, RM1, RM2.
      clear - AS_PHI DJ_PHI_FS HGTFS HFS64 NFSW HFSub HspH HspA SB1 SB2 SB3 SB4 SB5 SB6 SH1 SH2 SH3 SH4 SH5 SH6
        Hge HSS HFN HCMK HSZ HSZ'.
      f36_dj_split; f36_num. } }
  { intros DT' TS' C' T' DB' k' HT'.
    assert (HOUT : Forall (fun d => forall x, fst d <= x < snd d -> outside (@nil ivl) x)
                     (fp_tls (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                        (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0)).
    { apply Forall_forall. intros d _ x _. exact I. }
    destruct (fl_tls_same mem mem [] (AC.as_tp AC.ASYMS)
                (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0
                DT' TS' C' T' DB' k' HTLS HT' (munch_refl (@nil ivl) mem) HOUT)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT' TS' C' T' DB' k'.
    destruct (f36_fs_ranges FS) as
      (Rh0 & Rh1 & Rh2 & Rf0 & Rf1 & Rf2 & RM0 & RM1 & RM2 & Rfr0 & Rfr0' & Rfr1 & Rfr1' & Rfr2 & Rfr2').
    unfold fp_dj, fp_w, fp_w1. cbn [flat_map app fp_tls].
    rewrite Rfr0, Rfr0', Rfr1, Rfr1', Rfr2, Rfr2', Rh0, Rh1, Rh2, Rf0, Rf1, Rf2, RM0, RM1, RM2.
    clear - AS_C AS_T AS_DB DJ_C_FS DJ_T_FS DJ_DB_FS HGTFS HFS64 NFSW HFSub SB1 SB2 SB3 SB4 SB5 SB6
      SH1 SH2 SH3 SH4 SH5 SH6 HC0rng HT0rng HDBzr NC0 NT0 NDB0 HspH HspA HSS HFN HCMK HSZ HSZ'
      NC NT NDB Hstklo HS4 Hsp64 EDTu ETSu ETu ECw EDBw.
    f36_dj_split.
    all: rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
    all: f36_num. }
Qed.

(* FRA and ENT across n stores into the frame's own FRAME_SHADOW (392) shadow bytes at S(fr) + o (the slot /
   count-variable shadow stores 0x82c40-0x82c4c and 0x82c88): FRA by Tac_slot.sl_fr_meta, ENT by Tac_slot.ent_store
   (every written byte is a shadow byte of the frame); AH, stklo, stkhi and the owned set by a_fs_ok_store_AH. *)
Lemma f36_fra_meta : forall g fr hb regs regs' mem mem' md (o n : Z),
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  0 <= o -> 0 < n -> o + n <= FRAME_SHADOW ->
  munch [(Sfr fr + o, Sfr fr + o + n)] mem mem' -> wmono rsegs mem mem' ->
  (forall x, Sfr fr + o <= x < Sfr fr + o + n -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md o n HFRA HENT Ho Hn Hon MU WM HnewP E2 E3 E4 E8 E9 E19 E26.
  pose proof (f36_fra_loc g fr hb regs mem md HFRA)
    as (FS & (FSw & HFSw & EFS) & HGTFS & HFSlo & HFSapp & Hhi & Hfr0 & HGTfr & Hfrapp & Hfrloc).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 &
    (sh & Hsh & Hshl) & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  set (S3 := Sfr fr) in *.
  assert (HSh : forall x, S3 <= x < S3 + FRAME_SHADOW ->
    in_shadow x /\ shadow_addr (fr + 8 * (x - S3)) = x /\ fr <= fr + 8 * (x - S3) < fr + FRAME_BYTES).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - S3)) = x)
      by (rewrite f36_sh_frame_of by lia; unfold S3, Sfr; lia).
    split; [rewrite <- E; apply shadow_of_app, Hfrapp; lia | split; [exact E | lia]]. }
  pose proof (f36_in_shadow_bnd _ (proj1 (HSh S3 ltac:(lia)))) as HS3a.
  pose proof (f36_in_shadow_bnd _ (proj1 (HSh (S3 + FRAME_SHADOW - 1) ltac:(lia)))) as HS3b.
  set (W := [(S3 + o, S3 + o + n)]) in *.
  assert (HWsh : forall x, S3 + o <= x < S3 + o + n -> in_shadow x) by (intros x Hx; apply HSh; lia).
  assert (HWapp : forall x, app_mem x -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin. exact (app_not_shadow x Hx (HWsh x Hin)). }
  assert (HWhi : forall x, HIGHMEM_BEG <= x -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
    pose proof (f36_in_shadow_bnd _ (HWsh x Hin)). lia. }
  assert (HWsh2 : forall x, ~ (S3 <= x < S3 + FRAME_SHADOW) -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. lia. }
  assert (HpresM : forall x, 0 <= x < 2 ^ 64 -> (exists b, mrd rsegs mem (wa x) = Some b) ->
    exists b, mrd rsegs mem' (wa x) = Some b).
  { intros x Hx Hp. destruct (Z_le_gt_dec (S3 + o) x); [destruct (Z_lt_ge_dec x (S3 + o + n))|].
    - apply HnewP. lia.
    - unfold mrd in *. rewrite MU; [exact Hp|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia | exact I].
    - unfold mrd in *. rewrite MU; [exact Hp|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia | exact I]. }
  assert (Hsh' : exists sh', bytes_at rsegs mem' S3 sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
  { rewrite FRAME_SHADOW_val in Hshl |- *. change (Z.to_nat 392) with 392%nat in Hshl |- *.
    apply f36_ba_present; [unfold LOWMEM_END in *; lia | unfold HIGHMEM_BEG in *; lia |].
    intros i Hi. apply HpresM; [unfold LOWMEM_END, HIGHMEM_BEG in *; lia|].
    apply (f36_ba_some mem S3 sh); [exact Hsh | rewrite Hshl; lia]. }
  assert (HroM : ro_agree rsegs mem').
  { apply (sl_ro_keep W mem mem' Hro MU). intros x Hx. apply HWapp.
    unfold app_mem, LOWMEM_END; left; unfold AC.GT in Hx; lia. }
  assert (Hrtdj : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN.
    unfold LOWMEM_END in HS3a. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  rewrite EFS in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { change (AC.as_tp AC.ASYMS) with RT_TP. rewrite <- EFS.
    exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  assert (Hfsz : FS + AC.FS_SIZE <= 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hmeta : forall q, fs_meta FS q -> outside W q).
  { intros q Hq. apply HWapp. apply HFSapp. split; [exact (f36_fs_meta_ge FS q Hq)|].
    pose proof (fs_meta_below FS q Hq). unfold AC.FS_SIZE. lia. }
  assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (STKLO mem md) q -> ~ (FS <= q < FS + AC.FS_SIZE) ->
    ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) -> mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
  { intros q Hq Hns Hnf Hnsh. apply MU. rewrite unsigned_lit by lia. cbn [outside]. split; [|exact I].
    intros Hin. destruct (HSh q ltac:(lia)) as (_ & Eq & Hb).
    destruct Hfrloc as [[Hlo Hhi'] | [Hlo Hhi']].
    - apply Hns. apply (f36_store_ok_sh _ _ q (fr + 8 * (q - S3))); [symmetry; exact Eq | lia].
    - apply Hnsh. exists (fr + 8 * (q - S3)). split; [lia | symmetry; exact Eq]. }
  destruct (a_fs_ok_store_AH AC.ASYMS _ _ _ _ W _ mem mem' md FS LAWS HAH Hwm HFSr Hfsz MU
              (fun q _ Hw => WM _ Hw) (fun q Hq Hp => HpresM q Hq Hp) Hmeta Hagree) as (HAH' & Hown' & HSTK & HSTKHI).
  assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
  { intros a Hin. pose proof (f36_ag_bound a Hin) as Hab.
    apply (f36_addr_keep W mem mem' a 1 (HAG a Hin) MU). intros i Hi.
    assert (Hlt : shadow_addr (a + i) < S3)
      by (unfold S3, Sfr; apply f36_sh_lt; [exact Hfr8 | unfold AC.GT in HGTfr; lia]).
    apply HWsh2. lia. }
  assert (HENT' : ENT APIf g hb mem' md).
  { eapply ent_store with (W := W) (fr := fr) (regs := regs);
      [ exact HENT | exact HFRA | exact (proj1 (fr_munch_ul _ _ _) MU) | | exact HSTK | exact HSTKHI
      | intros a _ Ho2; exact (proj2 (Hown' a) Ho2) ].
    intros x Hx. destruct (Z_le_gt_dec (S3 + o) x) as [D1|D1];
      [destruct (Z_lt_ge_dec x (S3 + o + n)) as [D2|D2]|].
    - right; right; right. unfold S3 in *. lia.
    - left. apply (proj2 (fr_outside_lib _ _)). unfold W. cbn [outside]. split; [lia | exact I].
    - left. apply (proj2 (fr_outside_lib _ _)). unfold W. cbn [outside]. split; [lia | exact I]. }
  split; [|exact HENT'].
  apply (sl_fr_meta B APIf ra empty FF g fr _ regs regs' mem mem' md W HFRA MU WM HroM Hrtdj HAH' HSTK
           Hfrapp HGTfr Hsh').
  - intros x Hx Hn1 Hn2. exact (HWsh2 x Hn2).
  - intros A1 HA1 HA1r x Hx.
    assert (EA : A1 = A) by (apply (f36_reg_eq regs 9 A1 A HA1 Hr9 HA1r HA64)).
    apply HWhi. lia.
  - intros x Hx. apply HWhi. lia.
  - intros A1 HA1 HA1r x Hx.
    assert (EA : A1 = A) by (apply (f36_reg_eq regs 9 A1 A HA1 Hr9 HA1r HA64)).
    apply HWhi. lia.
  - intros x Hx. left. apply HWhi. unfold AF.SLOT_STACK in *. lia.
  - exact HAG'.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.

(* FRA across the callee's run: it writes its own window [sp - 9136, sp), the class-0/1/2 side-stack bytes and the
   shadow of its window.  RT by RT_meta_write (every shadow byte is readable again: the callee's shadow_rw), AH and
   stklo by a_laws_fs_store (the written bytes are the window, the side stack or the shadow of either), and every
   other FRA cell is outside the write set: the low image, the frame body and its FRAME_SHADOW (392) shadow bytes
   (the cut keeps the frame apart from the classes 0-2 and the window), the spills at [s1 + 40, s1 + 56) and
   [s1 + 336] and the saved registers (above sp), and the entry window (still backed inside [sp - 9136, sp)). *)
Lemma f36_fra_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  STKLO mem' md = STKLO mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 56 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 336 <= x < bv_unsigned (getr regs 9) + 344 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' HREC HIN E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA416|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split; [|exact (HREC Hrec)]].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (f36_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  (* FRA's input facts: the call writes no byte of the input block and no shadow byte of it *)
  refine (fra_in_keep_sh g mem mem' W Hinb Hinblk _ _).
  - first [exact MU | exact (proj1 (fr_munch_ul _ _ _) MU) | exact (proj2 (fr_munch_ul _ _ _) MU)].
  - intros x Hx. destruct (HIN x Hx) as (H1 & H2). split.
    + first [exact H1 | apply (proj2 (fr_outside_lib _ _)); exact H1
            | apply (proj1 (fr_outside_lib _ _)); exact H1].
    + first [exact H2 | apply (proj2 (fr_outside_lib _ _)); exact H2
            | apply (proj1 (fr_outside_lib _ _)); exact H2].
Qed.

(* A shadow byte of the frame is outside the call's writes: it is not an application byte (so it misses the
   window and the nine side-stack bands), and the frame is apart from the class-0/1/2 frames and from the
   window, so its granule misses their shadow. *)
Lemma f36_out_frsh : forall S FS fr t,
  0 <= FS -> FS + FS_SIZE <= S - CM_K -> S <= APPMEM_END ->
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - CM_K <= a < S -> app_mem a) ->
  0 <= fr -> fr mod 8 = 0 -> FS + 3182592 <= fr ->
  (fr + FRAME_BYTES <= S - CM_K \/ S <= fr) ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  Sfr fr <= t < Sfr fr + FRAME_SHADOW ->
  outside (f36_W S FS) t.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros S FS fr t HFS0 HFSS HSA HFSapp HWapp Hfr0 Hfr8 HfrFS Hdj Hfrapp Ht.
  assert (HSZ : FS_SIZE = 11571200) by reflexivity.
  assert (Hish : in_shadow t).
  { assert (E : shadow_addr (fr + 8 * (t - Sfr fr)) = t)
      by (rewrite f36_sh_frame_of by (unfold Sfr in *; lia); unfold Sfr in *; lia).
    rewrite <- E. apply shadow_of_app. apply Hfrapp. unfold Sfr in *. lia. }
  rewrite f36_W_eq. cbn [outside].
  repeat split.
  - intros HC. exact (app_not_shadow t (HWapp t HC) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - exact (f36_sh_dj fr (FS + 36864) (FS + 1085440) t Hfr8 Hfr0 ltac:(lia) ltac:(lia)
             ltac:(right; lia) Ht).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - exact (f36_sh_dj fr (FS + 1085440) (FS + 2134016) t Hfr8 Hfr0 ltac:(lia) ltac:(lia)
             ltac:(right; lia) Ht).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - intros HC. exact (app_not_shadow t (HFSapp t ltac:(lia)) Hish).
  - exact (f36_sh_dj fr (FS + 2134016) (FS + 3182592) t Hfr8 Hfr0 ltac:(lia) ltac:(lia)
             ltac:(right; lia) Ht).
  - exact (f36_sh_dj fr (S - CM_K) S t Hfr8 Hfr0 ltac:(lia) ltac:(unfold CM_K; lia) Hdj Ht).
Qed.

Lemma f36_meta_out : forall g fr hb regs mem md o n,
  FRA B APIf ra g fr hb regs mem md -> 0 <= o -> 0 < n -> o + n <= FRAME_SHADOW ->
  0 <= fr /\ fr mod 8 = 0 /\ AC.GT <= fr /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\
  LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG /\
  (forall x, app_mem x -> outside [(Sfr fr + o, Sfr fr + o + n)] x) /\
  (forall x, HIGHMEM_BEG <= x -> outside [(Sfr fr + o, Sfr fr + o + n)] x) /\
  (forall x, x < LOWMEM_END -> outside [(Sfr fr + o, Sfr fr + o + n)] x) /\
  (forall y, 0 <= y -> ~ (fr <= y < fr + FRAME_BYTES) -> outside [(Sfr fr + o, Sfr fr + o + n)] (shadow_addr y)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md o n HFRA Ho Hn Hon.
  pose proof (f36_fra_loc g fr hb regs mem md HFRA)
    as (FS & _ & _ & _ & _ & _ & Hfr0 & HGTfr & Hfrapp & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  assert (HSh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = x)
      by (rewrite f36_sh_frame_of by (unfold Sfr in *; lia); unfold Sfr in *; lia).
    rewrite <- E. apply shadow_of_app. apply Hfrapp. unfold Sfr in *. lia. }
  pose proof (f36_in_shadow_bnd _ (HSh (Sfr fr) ltac:(lia))) as HB1.
  pose proof (f36_in_shadow_bnd _ (HSh (Sfr fr + FRAME_SHADOW - 1) ltac:(lia))) as HB2.
  split; [exact Hfr0|]. split; [exact Hfr8|]. split; [exact HGTfr|]. split; [exact Hfrapp|].
  split; [lia|]. split; [lia|].
  split.
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
    exact (app_not_shadow x Hx (HSh x ltac:(lia))). }
  split; [intros x Hx; cbn [outside]; split; [lia | exact I]|].
  split; [intros x Hx; cbn [outside]; split; [lia | exact I]|].
  intros y Hy0 Hny. cbn [outside]. split; [|exact I]. intros Hin.
  pose proof (f36_sh_frame fr y (shadow_addr y - Sfr fr) Hfr0 Hfr8 Hy0 ltac:(unfold Sfr in *; lia)) as Hz.
  apply Hny. lia.
Qed.

(* 0x82c94 mv a0,s2 ; 0x82c98 mv a1,s4 ; 0x82c9c jal reac_box_catalogue_match -> 0x82ca0, by the callee's
   contract (which asks for mem_inv: f36_evt_call_ro below reaches it from ro_agree). *)
Lemma f36_evt_call : reac_box_catalogue_match_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s2 = Z_to_bv 64 phi -> s4 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi fb /\ (phi + 50 <= S - CM_K \/ S <= phi)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m phi 50 /\ app_mem (phi + 50)) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82ca0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x82ca0) fc None m' (seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82c94) fc None m (seg_rom rsegs)).
Proof.
  intros CMCx ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb -> -> -> Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HMI HAC HSW
    Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  step. (* 0x82c94 mv a0,s2 *)
  step. (* 0x82c98 mv a1,s4 *)
  step. (* 0x82c9c jal 84e40 <reac_box_catalogue_match> *)
  pose proof CMCx as HC. unfold reac_box_catalogue_match_contract, REAC_BOX_CATALOGUE_MATCH in HC.
  eapply evt_cut.
  { eapply HC with (f := phi) (len := len) (S := S) (FS := FS) (fb := fb).
    all: cbv zeta.
    all: first [ exact HST | exact HROM | exact Hfb | exact HFB | exact HROc | exact HMI | exact HAC | exact HSW
               | exact HADW | exact HADf | exact HADT | exact HADB | exact HRB | exact HRM | exact HGC
               | exact HC254 | exact HC255 | exact HFP | exact HTLS | exact Hmod
               | reflexivity | (f_equal; lia) | lia ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & AC' & SW' & AD' & FP' & TL').
  subst ms'.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. cbv beta. do 15 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC'|]. split; [exact SW'|]. split; [exact AD' | exact FP'].
Qed.

(* ---- the call on the cut's own memory: ro_agree in place of mem_inv (FRA carries ro_agree only), as F35's
   f35_evt_ro. The run is taken on the normalized memory (mem_inv_normalize), where the read-side premises hold by
   the mem_rel moves below and Seg/Tac_ro.v's, and MemNorm.evt_normalize carries it back. Every address of the
   side stack is at or above GT = 0x5fe000, above every segment of the image, so normalizing changes no byte and
   no writability there (f36_ro_ge). ---- *)
Lemma f36_ro_ge : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  destruct (BzBridge.find_segment_below rsegs 0x5fe000 (bv_unsigned (wa a)) 1 s f36_segs_below E ltac:(lia))
    as [L|L]; [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia].
Qed.

Lemma f36_stk_rel_ge : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi HR Hlo Hhi.
  assert (WV : forall a, lo <= a < hi -> (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None)).
  { intros a Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (f36_ro_ge a ltac:(lia))). split; auto. }
  split; intros (H0 & H1 & H); (split; [lia|]); (split; [lia|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb); split.
  - apply (proj2 (WV a Ha)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
  - apply (proj1 (WV a Ha)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f36_fs_place_rel : forall m m0 FS, mem_rel rsegs m m0 -> (fs_place m FS <-> fs_place m0 FS).
Proof.
  intros m m0 FS HR. unfold fs_place.
  split; intros (H1 & H2 & H3 & H4 & H5); (split; [exact H1|]); (split; [exact H2|]); (split; [exact H3|]);
    (split; [exact H4|]); pose proof H5 as (_ & Hhi & _); unfold ASAN_GT in H3.
  - exact (proj1 (f36_stk_rel_ge m m0 FS (FS + FS_SIZE) HR ltac:(lia) Hhi) H5).
  - exact (proj2 (f36_stk_rel_ge m m0 FS (FS + FS_SIZE) HR ltac:(lia) Hhi) H5).
Qed.

Lemma f36_tls_rel : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k HR.
  pose proof (fun a bs => bytes_at_rel rsegs m m0 a bs HR) as BR.
  unfold asan_tls_cells. repeat setoid_rewrite BR. reflexivity.
Qed.

Lemma f36_fp_cls_rel : forall m m0 FS c, mem_rel rsegs m m0 -> (fp_cls m FS c <-> fp_cls m0 FS c).
Proof.
  intros m m0 FS c HR. pose proof (fun a bs => bytes_at_rel rsegs m m0 a bs HR) as BR.
  unfold fp_cls. repeat setoid_rewrite BR. reflexivity.
Qed.

Lemma f36_fp_rel : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  (fp cs m TP FS lo hi W D <-> fp cs m0 TP FS lo hi W D).
Proof.
  intros cs m m0 TP FS lo hi W D HR.
  assert (FC : Forall (fp_cls m FS) cs <-> Forall (fp_cls m0 FS) cs).
  { split; apply Forall_impl; intros c; apply (f36_fp_cls_rel m m0 FS c HR). }
  pose proof (fun a bs => bytes_at_rel rsegs m m0 a bs HR) as BR.
  pose proof (fun DT TS C T DB k => f36_tls_rel m m0 TP DT TS C T DB k HR) as TR.
  unfold fp. setoid_rewrite (f36_fs_place_rel m m0 FS HR). setoid_rewrite FC. setoid_rewrite TR.
  repeat setoid_rewrite BR. reflexivity.
Qed.

Lemma f36_cmtls_rel : forall m m0 TP FS lo hi, mem_rel rsegs m m0 ->
  (reac_box_catalogue_match_tls m TP FS lo hi <-> reac_box_catalogue_match_tls m0 TP FS lo hi).
Proof.
  intros m m0 TP FS lo hi HR. unfold reac_box_catalogue_match_tls.
  pose proof (fun DT TS C T DB k => f36_tls_rel m m0 TP DT TS C T DB k HR) as TR.
  setoid_rewrite TR. reflexivity.
Qed.

Lemma f36_shadow_rw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (Tac_ro.wview_hi m m0 a HR ltac:(unfold LOWMEM_END; lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f36_addressable_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma f36_evt_call_ro : reac_box_catalogue_match_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s2 = Z_to_bv 64 phi -> s4 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi fb /\ (phi + 50 <= S - CM_K \/ S <= phi)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m phi 50 /\ app_mem (phi + 50)) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82ca0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x82ca0) fc None m' (seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x82c94) fc None m (seg_rom rsegs)).
Proof.
  intros CMCx ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb E2 E4 Esp Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HRO HAC HSW
    Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hlo0 : LOWMEM_END <= S - CM_K) by (unfold HIGHMEM_BEG, LOWMEM_END in *; lia).
  assert (HS64 : S <= 2 ^ 64) by lia.
  assert (HFB0 : 50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs (normalize rsegs m) phi fb /\
                              (phi + 50 <= S - CM_K \/ S <= phi)).
  { intros H50. destruct (HFB H50) as (X1 & X2 & X3 & X4).
    split; [exact X1|]. split; [exact X2|]. split; [exact (Tac_ro.ba_rel m _ _ _ REL X3) | exact X4]. }
  assert (HROc0 : forall a, CM_T <= a < CM_T + 3256 ->
                    mrd rsegs (normalize rsegs m) (wa a) = seg_rom rsegs (wa a)).
  { intros a Ha. rewrite <- (mrd_rel rsegs m _ (wa a) REL). exact (HROc a Ha). }
  assert (HADf0 : 50 <= len -> addressable (normalize rsegs m) phi 50 /\ app_mem (phi + 50)).
  { intros H50. destruct (HADf H50) as (X1 & X2). split; [exact (Tac_ro.addressable_rel m _ _ _ REL X1) | exact X2]. }
  pose proof (f36_evt_call CMCx ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc (normalize rsegs m) phi len S FS fb E2 E4 Esp Hphi Hlen HS Hmod HKS
    (Tac_ro.stk_rel m _ _ _ REL Hlo0 HS64 HST) HROM Hfb HFB0 HROc0
    (mem_inv_normalize rsegs m) (Tac_ro.asan_cells_rel m _ REL HAC) (Tac_ro.shadow_rw_rel m _ REL HSW)
    Hhi Hsp (Tac_ro.addressable_rel m _ _ _ REL HADW) HADf0
    (Tac_ro.addressable_rel m _ _ _ REL HADT) (Tac_ro.addressable_rel m _ _ _ REL HADB)
    (Tac_ro.ba_rel m _ _ _ REL HRB) (Tac_ro.ba_rel m _ _ _ REL HRM) (Tac_ro.ba_rel m _ _ _ REL HGC)
    (Tac_ro.ba_rel m _ _ _ REL HC254) (Tac_ro.ba_rel m _ _ _ REL HC255)
    (proj1 (f36_fp_rel _ m _ _ _ _ _ _ _ REL) HFP) (proj1 (f36_cmtls_rel m _ _ _ _ _ REL) HTLS)) as HC.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply LE.evt_mono; [exact HN|].
  intros ms (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
              E & MU & WM & MI' & ST' & AC' & SW' & AD' & FP') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exact (Tac_ro.stk_rel_back memX m0' _ _ Hmr Hlo0 HS64 ST')|].
  split; [exact (f36_shadow_rw_back memX m0' Hmr SW')|].
  split; [exact (f36_addressable_back memX m0' _ _ Hmr AD')|].
  exact (proj2 (f36_fp_rel _ memX m0' _ _ _ _ _ _ Hmr) FP').
Qed.

(* ===================== the shadow-store and machine-run helpers of the row branch, the joins and the latch ======== *)

(* n shadow bytes of the frame at S(fr) + o are readable and writable (the runtime's shadow_rw). *)
Lemma f36_shadow_stk : forall g fr hb regs mem md o n,
  FRA B APIf ra g fr hb regs mem md -> 0 <= o -> 0 < n -> o + n <= FRAME_SHADOW ->
  stk rsegs mem (Sfr fr + o) (Sfr fr + o + n).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md o n HFRA Ho Hn Hon.
  destruct (f36_meta_out g fr hb regs mem md o n HFRA Ho Hn Hon) as (Hfr0 & Hfr8 & HGTfr & Hfrapp & HB1 & HB2 & _).
  pose proof HFRA as (A & sp & s5 & HRT & _).
  assert (HSh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = x)
      by (rewrite f36_sh_frame_of by (unfold Sfr in *; lia); unfold Sfr in *; lia).
    rewrite <- E. apply shadow_of_app. apply Hfrapp. unfold Sfr in *. lia. }
  split; [unfold LOWMEM_END in *; lia|]. split; [unfold HIGHMEM_BEG in *; lia|].
  intros a Ha. exact (RT_shadow_rw _ _ _ HRT a (HSh a ltac:(lia))).
Qed.

(* BLK reads memory only through the side stack's base word at tp (in the low image). *)
Lemma f36_blk_keep : forall g j phi fr m m' W, BLK g j phi fr m -> munch W m m' ->
  (forall x, 0 <= x < 6283264 -> outside W x) -> BLK g j phi fr m'.
Proof.
  intros g j phi fr m m' W HB MU HW x Hx. destruct (HB x Hx) as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|].
  intros (b & Hb & Hw & Hbx). apply H3. exists b. split; [exact Hb|]. split; [|exact Hbx].
  apply (f36_word_mem_back W m m' _ b MU); [|exact Hw].
  intros y Hy. change (AC.as_tp AC.ASYMS) with RT_TP in Hy. unfold RT_TP in Hy.
  rewrite MState.unsigned_lit by lia. apply HW. lia.
Qed.

Lemma f36_wr_stk : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Ha Hn Hn0. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma f36_store_ok1 : forall m lo hi a, stk rsegs m lo hi -> lo <= a < hi -> store_ok rsegs m (wa a) 1 = true.
Proof.
  intros m lo hi a H Ha. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  apply (wr_at_store_ok rsegs m a 1 0 1%nat); [apply (f36_wr_stk m lo hi a 1 H); lia | lia | lia].
Qed.

Lemma f36_rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H.
  pose proof (bytes_at_ov_read rsegs m a (le8 v) 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH.
Qed.

(* One byte stored inside [lo, hi) of a stack range: the range, the write set and the other bytes. *)
Definition f36_SP (m0 m : word -> option byte) (lo hi : Z) : Prop :=
  munch [(lo, hi)] m0 m /\ wmono rsegs m0 m /\ stk rsegs m lo hi /\
  (forall c cs, bytes_at rsegs m0 c cs -> (c + Z.of_nat (length cs) <= lo \/ hi <= c) -> bytes_at rsegs m c cs).

Lemma f36_SP_refl : forall m lo hi, stk rsegs m lo hi -> f36_SP m m lo hi.
Proof.
  intros m lo hi H. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact H|].
  intros c cs Hc _. exact Hc.
Qed.

Lemma f36_SP_store_ok : forall m0 m lo hi a, f36_SP m0 m lo hi -> lo <= a < hi -> store_ok rsegs m (wa a) 1 = true.
Proof. intros m0 m lo hi a (_ & _ & H & _) Ha. exact (f36_store_ok1 m lo hi a H Ha). Qed.

(* One byte stored inside [lo, hi) of a stack range keeps the range, the write set and the other bytes. *)
Lemma f36_SP_st : forall m0 m a bs lo hi, length bs = 1%nat ->
  f36_SP m0 m lo hi -> lo <= a < hi -> f36_SP m0 (write_to_mem m (wa a) bs) lo hi.
Proof.
  intros m0 m a bs lo hi Hl (MU & WM & HST & K) Ha. pose proof HST as (H0 & H1 & _).
  split; [apply munch_write; [exact MU | lia | rewrite Hl; lia | rewrite Hl; cbn [inside]; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [apply stk_write; [exact HST | lia | rewrite Hl; lia]|].
  intros c cs Hc Hd. apply bytes_at_write_other; [exact (K c cs Hc Hd) | lia | rewrite Hl; lia |].
  rewrite Hl. lia.
Qed.

Ltac f36_sb lo hi a :=
  match goal with
  | P : f36_SP ?m0 ?mm lo hi |- _ =>
      pose proof (f36_SP_store_ok m0 mm lo hi a P ltac:(lia)) as _ST;
      step;
      match goal with
      | |- LE.evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?aa ?bs) _) =>
          let P' := fresh "P" in
          pose proof (f36_SP_st m0 mm a bs lo hi ltac:(reflexivity) P ltac:(lia)) as P';
          change (write_to_mem mm aa bs) with (write_to_mem mm (wa a) bs);
          clear P _ST;
          set (write_to_mem mm (wa a) bs) in *
      end
  end.

(* 0x82c38 bnez s8,82c40 (taken: s8 = the row address, not 0, so the error path 0x82c3c beqz a0,82fa0 is not
   reached); 0x82c40-0x82c4c sb s11,8..11(s3) (the four shadow bytes S3 + 8 .. S3 + 11 become 0xf8); 0x82c50
   li s6,1 -> 0x82c54. Touched: [S3 + 8, S3 + 12) written. *)
Lemma f36_evt_pre :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 rw : Z),
    s3 = Z_to_bv 64 S3 -> s8 = Z_to_bv 64 rw -> s11 = Z_to_bv 64 (-8) -> 0 < rw < 2 ^ 64 ->
    stk rsegs m (S3 + 8) (S3 + 12) ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                                         (Z_to_bv 64 1) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    Fr (Z_to_bv 64 0x82c54) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (S3 + 8) (S3 + 12) /\
         (forall c cs, bytes_at rsegs m c cs -> (c + Z.of_nat (length cs) <= S3 + 8 \/ S3 + 12 <= c) ->
            bytes_at rsegs m' c cs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c38) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m S3 rw -> -> -> Hrw HST.
  (* 0x82c38 bnez s8,82c40: taken *)
  step. rewrite (f36_eqb_lit rw 0) by lia. first [if_true | if_false].
  pose proof (f36_SP_refl m (S3 + 8) (S3 + 12) HST) as P0.
  (* 0x82c40 .. 0x82c4c sb s11,8..11(s3) *)
  f36_sb (S3 + 8) (S3 + 12) (S3 + 8).
  f36_sb (S3 + 8) (S3 + 12) (S3 + 9).
  f36_sb (S3 + 8) (S3 + 12) (S3 + 10).
  f36_sb (S3 + 8) (S3 + 12) (S3 + 11).
  (* 0x82c50 li s6,1 *)
  match goal with P : f36_SP m ?mm _ _ |- _ =>
    step;
    apply evt_done; exists mm; split; [reflexivity|];
    destruct P as (MU & WM & HST' & K); split; [exact MU|]; split; [exact WM|]; split; [exact HST' | exact K]
  end.
Qed.

Lemma f36_ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma f36_eqb_ne : forall x y : word, x <> y -> bv_eqb x y = false.
Proof. intros x y H. unfold bv_eqb. apply Z.eqb_neq. intros E. apply H. apply bv_eq. exact E. Qed.

(* 0x82c54 beqz a0,82c88 with a0 = 0 (the block is row i's declaration): taken. *)
Lemma f36_evt_hit :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                             t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m ->.
  step. try first [if_true | if_false].
  apply evt_done. reflexivity.
Qed.

(* The row latch with a0 <> 0 (the block is not row i's declaration): 0x82c54 beqz falls through, 0x82c58 j 82c70,
   0x82c70 ld a0,160(s1) (a0 = c = fr + 32), 0x82c74 ld a0,0(a0) (a0 = 11, the row count), 0x82c78 addi s9,s9,1,
   0x82c7c addi s7,s7,296, 0x82c80 bltu s9,a0,82be4. Touched: reads [A + 160, A + 168) and [c, c + 8). *)
Ltac f36_latch_pre H0 :=
  step; rewrite ?H0; try first [if_true | if_false];
  step; step; step; step; step; step.

(* i + 1 < 11: the row head 0x82be4 li a0,296; mulh a1,s9,a0; mul a0,s9,a0; srai a2,a0,0x3f -> 0x82bf4. *)
Lemma f36_evt_next :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z) (i : nat),
    s1 = Z_to_bv 64 A -> bv_eqb a0 (Z_to_bv 64 0) = false -> s9 = Z_to_bv 64 (Z.of_nat i) ->
    s7 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i) -> (i < 10)%nat ->
    ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 c)) ->
    ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (CAT_ROW * Z.of_nat (S i)))
                             (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                             (Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat (S i))) s8 (Z_to_bv 64 (Z.of_nat (S i)))
                             s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x82bf4) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c i -> H0 -> -> Hi RD160 RDc.
  step. rewrite H0. cbv iota.
  step. step. step. step. step. step.
  rewrite (f36_ltu_lit (Z.of_nat i + 1) 11) by lia. first [if_true | if_false].
  step. step. step. step.
  apply evt_done.
  do 10 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

(* i + 1 = 11: 0x82c80 bltu falls through; 0x82c84 li s7,0 -> 0x82c88. *)
Lemma f36_evt_last :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z),
    s1 = Z_to_bv 64 A -> bv_eqb a0 (Z_to_bv 64 0) = false -> s9 = Z_to_bv 64 10 ->
    ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 c)) ->
    ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
    LE.evt rsegs
      (fun ms' => exists s7', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
                                        s5 s6 (Z_to_bv 64 0) s8 s7' s10 s11 t3 t4 t5 t6)
                                   Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c -> H0 -> RD160 RDc.
  step. rewrite H0. cbv iota.
  step. step. step. step. step. step.
  try first [if_true | if_false].
  step.
  apply evt_done. eexists. reflexivity.
Qed.

(* 0x82c88 sb s11,4(s3) (the shadow byte S3 + 4 of the count variable at fr + 32 becomes 0xf8); j 82c94.
   Touched: [S3 + 4, S3 + 5) written. *)
Lemma f36_evt_c24 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 : Z),
    s3 = Z_to_bv 64 S3 -> stk rsegs m (S3 + 4) (S3 + 5) ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
                                         s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    Fr (Z_to_bv 64 0x82c94) fc None m' (seg_rom rsegs) /\
         f36_SP m m' (S3 + 4) (S3 + 5))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m S3 -> HST.
  pose proof (f36_SP_refl m (S3 + 4) (S3 + 5) HST) as P0.
  f36_sb (S3 + 4) (S3 + 5) (S3 + 4).
  step.
  match goal with P : f36_SP m ?mm _ _ |- _ => apply evt_done; exists mm; split; [reflexivity | exact P] end.
Qed.

(* 0x82c90 li s7,0 -> 0x82c94. *)
Lemma f36_evt_c2c :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0)
                             s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c94) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c90) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evt_done. reflexivity. Qed.

(* 0x82c84 li s7,0 -> 0x82c88 (entered from the official Inv_B82c84_at: no row matched). Touched: none. *)
Lemma f36_evt_c20 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0)
                             s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x82c88) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82c84) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evt_done. reflexivity. Qed.

End Tac_f36.
