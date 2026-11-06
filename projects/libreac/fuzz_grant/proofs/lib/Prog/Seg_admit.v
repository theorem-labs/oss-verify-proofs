From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step Cells Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YO0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import LLVMFuzzerTestOneInput_c SlotNeeds_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantSlotPlan SlotBridge reac_headamp_tx_init_c memset_c GrantModel reac_grant_alloc_fits_c reac_grant_allocate_c RgLemmas.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import Seg_main.
Import ListNotations.
Open Scope Z_scope.

Lemma rd8_range : forall pl pos, 0 <= fst (rd8 pl pos) < 256.
Proof.
  intros pl pos. unfold rd8. destruct (pos <? length pl)%nat; cbn [fst]; [|lia].
  unfold pbz. pose proof (bv_unsigned_in_range _ (nth pos pl (Z_to_bv 8 0))) as H.
  change (bv_modulus 8) with 256 in H. lia.
Qed.

Lemma rd16_range : forall pl pos, 0 <= fst (rd16 pl pos) < 65536.
Proof.
  intros pl pos. unfold rd16.
  destruct (rd8 pl pos) as [lo p1] eqn:E1. destruct (rd8 pl p1) as [hi p2] eqn:E2. cbn [fst].
  pose proof (rd8_range pl pos) as H1. pose proof (rd8_range pl p1) as H2.
  rewrite E1 in H1. rewrite E2 in H2. cbn [fst] in H1, H2. lia.
Qed.

Lemma hdr_ranges : forall pl,
  0 <= h_u16 (header pl) < 65536 /\ -32768 <= h_base (header pl) < 32768 /\
  0 <= h_in (header pl) < 256 /\ 0 <= h_rows (header pl) < 256 /\
  (0 <= h_base (header pl) <-> h_u16 (header pl) < 32768).
Proof.
  intros pl. unfold header.
  destruct (rd16 pl 0) as [u p1] eqn:E1. destruct (rd8 pl p1) as [i p2] eqn:E2. destruct (rd8 pl p2) as [r p3] eqn:E3.
  pose proof (rd16_range pl 0) as H1. pose proof (rd8_range pl p1) as H2. pose proof (rd8_range pl p2) as H3.
  rewrite E1 in H1. rewrite E2 in H2. rewrite E3 in H3. cbn [fst] in *.
  unfold h_base, sext16; cbn [h_u16 h_in h_rows].
  destruct (u <? 32768) eqn:Eu; [apply Z.ltb_lt in Eu | apply Z.ltb_ge in Eu]; repeat split; lia.
Qed.

Lemma mem_inv_munch_wr : forall m m' o n,
  mem_inv rsegs m -> munch [(o, o + n)] m m' -> wr_at rsegs m o n -> mem_inv rsegs m'.
Proof.
  intros m m' o n HI HM (Ho & Hn & HW) a b Ha.
  pose proof (bv_unsigned_in_range _ a) as Ra. change (bv_modulus 64) with (2 ^ 64) in Ra.
  destruct (Z_lt_le_dec (bv_unsigned a) o) as [L|L];
    [| destruct (Z_lt_le_dec (bv_unsigned a) (o + n)) as [L2|L2]].
  - rewrite (HM a) in Ha by (cbn; lia). exact (HI a b Ha).
  - destruct (m a) eqn:Em.
    + exact (HI a b0 Em).
    + apply (wview_not_ro rsegs m a); [|exact Em].
      specialize (HW (bv_unsigned a - o) ltac:(lia)).
      replace (wa (o + (bv_unsigned a - o))) with a in HW; [exact HW|].
      unfold wa. replace (o + (bv_unsigned a - o)) with (bv_unsigned a) by lia.
      symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite (HM a) in Ha by (cbn; lia). exact (HI a b Ha).
Qed.

Lemma fits_z : reac_grant_alloc_fits_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (base width : Z),
  int32 base -> int32 width -> (0 <= base -> 1 <= width <= 40 -> base + width < 2 ^ 31) ->
  mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.b2z (fits base width))) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 base) (Z_to_bv 64 width) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 REAC_GRANT_ALLOC_FITS) fc None m (seg_rom rsegs)).
Proof.
  intros FITS ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m base width
    Hb Hw Hs HI.
  eapply evt_mono.
  - apply (FITS ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 base) (Z_to_bv 64 width) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m base width); auto.
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m.
    split; [exact E|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. exact HI.
Qed.

Lemma alloc_z : reac_grant_allocate_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (o base w : Z) (cs : list cell),
  0 < o -> o + 2 < 2 ^ 64 -> int32 base -> int32 w -> (0 <= base -> 1 <= w <= 40 -> base + w <= 2 ^ 31 - 1) ->
  cells_size cs = 2%nat -> rw_cells rsegs m o cs -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(o, o + 2)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       if fits base w
       then r = Z_to_bv 64 0 /\ rw_cells rsegs m' o [CB 2 [Z_to_bv 8 base; Z_to_bv 8 w]]
       else r = Z_to_bv 64 (-1) /\ rw_cells rsegs m' o cs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 base) (Z_to_bv 64 w) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 REAC_GRANT_ALLOCATE) fc None m (seg_rom rsegs)).
Proof.
  intros ALLOC ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o base w cs
    Ho Ho2 Hb Hw Hs Hsz HR HI.
  assert (HWR : wr_at rsegs m o 2) by (destruct HR as [_ HW]; rewrite Hsz in HW; exact HW).
  eapply evt_mono.
  - apply (ALLOC ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 base) (Z_to_bv 64 w) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o base w); auto.
    right. split; [lia|]. split; [lia|]. exact HWR.
  - intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & PO).
    exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|].
    replace (negb (o =? 0)) with true in PO by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
    cbn [andb] in PO. destruct (fits base w).
    + destruct PO as (Hr & HB & HM & HW).
      split; [exact HM|]. split; [exact HW|]. split; [exact (mem_inv_munch_wr m m' o 2 HI HM HWR)|].
      split; [exact Hr|]. split.
      * split; [cbn; split; [reflexivity | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        rewrite !le1_byte in HB. exact HB.
      * cbn. exact (wr_at_transport rsegs m m' o 2 HWR HW).
    + destruct PO as (Hr & ->). split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact HI|].
      split; [exact Hr | exact HR].
Qed.

Definition PC_MID : Z := 0x13338.
Definition Mid (x : slot_ctx) (t : Z) (ms : machine_state) : Prop :=
  body x PC_MID ms /\ x_n x < 2 ^ 26 /\ rg ms 8 = w64 t /\
  rg ms 25 = w64 (x_n x - Z.of_nat (pos_end (x_pl x))) /\
  rg ms 9 = w64 (Z.b2z (ok (x_pl x))) /\ rg ms 18 = w64 (h_rows (hd x)) /\ rg ms 19 = w64 (h_in (hd x)) /\
  rg ms 20 = w64 (h_base (hd x)) /\ slots x ms /\ cslot x (pos_end (x_pl x)) ms /\
  table x t (T_end (x_pl x)) ms /\ arrays x (ws_end (x_pl x)) (st_end (x_pl x)) ms /\
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) /\ I1 (T_end (x_pl x)).

Lemma shl48_neg : forall u, 0 <= u < 65536 ->
  (2 ^ 63 <= Z.shiftl (bv_unsigned (w64 u)) 48 mod 2 ^ 64 <-> 32768 <= u).
Proof.
  intros u Hu. unfold w64. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma fits_spec : forall b w, fits b w = true <-> (1 <= w <= 40 /\ 0 <= b /\ b + w <= 48).
Proof. intros b w. unfold fits. rewrite !andb_true_iff, !Z.leb_le. tauto. Qed.

Lemma fits_false : forall b w, ~ (1 <= w <= 40 /\ 0 <= b /\ b + w <= 48) -> fits b w = false.
Proof. intros b w H. destruct (fits b w) eqn:E; [apply fits_spec in E; contradiction | reflexivity]. Qed.

Lemma slti49_ok : forall b w, 1 <= w <= 40 -> 0 <= b < 32768 ->
  Z.b2z (Z.lxor ((b + w) mod 18446744073709551616) 9223372036854775808 <? 9223372036854775857) =
  Z.b2z (fits b w).
Proof.
  intros b w Hw Hb. rewrite zb_lxor_sign by (rewrite Z.mod_small; lia).
  rewrite Z.mod_small by lia. rewrite Z.mod_small by lia.
  destruct (fits b w) eqn:E.
  - apply fits_spec in E. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - replace (_ <? _) with false; [reflexivity|]. symmetry. apply Z.ltb_ge.
    destruct (Z_le_gt_dec (b + w) 48) as [L|L]; [|lia].
    assert (fits b w = true) by (apply fits_spec; lia). congruence.
Qed.

Lemma slti49_ok' : forall b w, 1 <= w <= 40 -> 0 <= b < 32768 ->
  Z.b2z (Z.lxor (b + w) 9223372036854775808 <? 9223372036854775857) = Z.b2z (fits b w).
Proof.
  intros b w Hw Hb. rewrite <- (slti49_ok b w Hw Hb). rewrite (Z.mod_small (b + w)) by lia. reflexivity.
Qed.

Ltac mid_close ESP Hgp Htp Hs0 Hs9 :=
  unfold Mid, body, common;
  cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem MS];
  repeat match goal with |- _ /\ _ => split end;
  try assumption;
  try (unfold w64, PC_MID; reflexivity);
  try (unfold slots, cslot, SPL, LLVM_FRAME; rewrite <- ESP; assumption);
  try (unfold rg, PropExec.getr, w64, SPL, LLVM_FRAME; cbn -[Z_to_bv]; rewrite <- ?ESP; reflexivity);
  try (unfold rg, PropExec.getr; cbn -[Z_to_bv w64]; first [exact Hgp | exact Htp | exact Hs0 | exact Hs9 | reflexivity]).

Lemma lbu_val : forall v, 0 <= v < 256 ->
  bv_unsigned (zext 64 (bv_extract 0 8 (le_bytes_to_word [Z_to_bv 8 v]))) = v.
Proof.
  intros v Hv. rewrite zext_extract_byte. unfold zxb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with 18446744073709551616.
  rewrite (Z.mod_small v) by lia. apply Z.mod_small. lia.
Qed.

Lemma fits_false_iff : forall b w, fits b w = false -> ~ (1 <= w <= 40 /\ 0 <= b /\ b + w <= 48).
Proof. intros b w E H. apply fits_spec in H. congruence. Qed.

Lemma rw_C2_zero : forall m A, rw_cells rsegs m A [C2 (Z_to_bv 64 0)] ->
  rw_cells rsegs m A [CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]].
Proof.
  intros m A [[Hwf Hb] Hw]. split; [split; [cbn; split; [reflexivity | exact I] |] | exact Hw].
  cbn [cells_bytes cbytes] in *. exact Hb.
Qed.

Lemma admit_tail : reac_grant_alloc_fits_contract -> reac_grant_allocate_contract ->
  forall x t ms, Mid x t ms ->
  evt rsegs (fun ms' => kept x [] ms ms' /\
    (ok (x_pl x) = true /\ At_mallocSW1 x t ms' \/ ok (x_pl x) = false /\ At_raw x t PC_RAW_NOK ms')) ms.
Proof.
  intros FITS ALLOC x t ms HM.
  pose proof (hdr_ranges (x_pl x)) as (Ru & Rb & Ri & Rr & Rs).
  fold (hd x) in Ru, Rb, Ri, Rr, Rs.
  assert (Eok : ok (x_pl x) = fits (h_base (hd x)) (h_in (hd x))) by reflexivity.
  assert (EQ : eqv_inv (fun ms' => kept x [] ms ms' /\
      (ok (x_pl x) = true /\ At_mallocSW1 x t ms' \/ ok (x_pl x) = false /\ At_raw x t PC_RAW_NOK ms'))).
  { apply eqv_and; [apply eqv_kept |].
    intros a b He [[Hok Ha] | [Hok Ha]]; [left | right]; split; try exact Hok.
    - exact (eqv_At_mallocSW1 x t a b He Ha).
    - exact (eqv_At_raw x t PC_RAW_NOK a b He Ha). }
  unfold Mid in HM. rewrite Eok in HM.
  apply evt_canon; [exact EQ|].
    destruct HM as (((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & Hpay & Hstk & Hinv & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                     Hsp & Hfr & Hal & Hlen & HSlt) & Hn & Hs0 & Hs9 & Hs1 & Hs2 & Hs3 & Hs4 &
                     Hslots & Hcs & Htab & Harr & HH & HI1).
    rewrite canon_MS by exact Hsvc. unfold mkR_of.
    unfold w64, PC_MID in Hpc. rewrite Hpc, Hrv, Hro.
    assert (E2 : reg_get (ms_regs ms) 2 = Z_to_bv 64 (SPL x)) by exact Hsp.
    assert (E20 : reg_get (ms_regs ms) 20 = Z_to_bv 64 (h_base (hd x))) by exact Hs4.
    assert (E19 : reg_get (ms_regs ms) 19 = Z_to_bv 64 (h_in (hd x))) by exact Hs3.
    assert (E9 : reg_get (ms_regs ms) 9 = Z_to_bv 64 (Z.b2z (fits (h_base (hd x)) (h_in (hd x))))) by exact Hs1.
    rewrite E2, E20, E19, E9.
    unfold slots, cslot in Hslots, Hcs. unfold table, arrays in Htab, Harr.
    destruct Htab as (Hblk & Ht16 & HTl & HT). destruct Harr as (Hwl & Hsl & HWS & HST). unfold blk in Hblk.
    unfold x_n in *. unfold SPL in *. unfold LLVM_STACK in *. unfold LLVM_FRAME, YO0d.ALLOC_STACK in *.
    unfold CTRL_HEADAMP_ROW in *. unfold CTRL_HEADAMP_BYTES in Hrow. cbn [map] in Hrow.
    remember (x_S x - 592) as SP eqn:ESP.
    remember (ms_mem ms) as m eqn:Em.
    assert (Slo : 0 <= x_S x - 8784) by (destruct Hstk as [Hz _]; lia).
    pose proof (munch_refl [(x_S x - 8784, x_S x)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    destruct (stk_split rsegs m (x_S x - 8784) (SP + 200) (x_S x) Hstk ltac:(lia)) as [ST STU]. clear Hstk.
    carve_frame 2%nat ST. rename FR into FRa.
    zstep. zstep. zstep.
    call (fits_z FITS).
    1-2: unfold int32; lia.
    1: intros; lia.
    1: assumption.
    zstep. if_cases HC1; zify_cond HC1; [exfalso; lia|].
    zstep. zstep. zstep. zstep. zstep.
    call (alloc_z ALLOC).
    1-2: lia.
    1-2: unfold int32; lia.
    1: intros; lia.
    2: eassumption.
    1: reflexivity.
    1: assumption.
    destruct (fits (h_base (hd x)) (h_in (hd x))) eqn:Ef.
    + destruct POST as (Hr0 & FRa2). subst x17.
      pose proof (proj1 (fits_spec _ _) Ef) as (Hw & Hb0 & Hbw).
      zstep. zstep. if_cases HC2; zify_cond HC2; [cbn [Z.b2z] in HC2; exfalso; lia|].
      zstep. zstep. if_cases HC3; zify_cond HC3; [| exfalso; lia].
      zstep. zstep. if_cases HC4; zify_cond HC4.
      { exfalso. cbn [firstn skipn] in HC4. rewrite lbu_val in HC4 by lia.
        rewrite ?Z.mod_small in HC4 by lia. lia. }
      zstep. zstep. if_cases HC5; zify_cond HC5.
      { exfalso. cbn [firstn skipn] in HC5. rewrite lbu_val in HC5 by lia. lia. }
      zstep. zstep. zstep. zstep.
      eapply stk_release in ST; [ | exact FRa2 | lia ]. cbn [cells_size csize Nat.add] in ST.
      replace (SP + 198 + Z.of_nat 2) with (SP + 200) in ST by lia.
      pose proof (stk_merge rsegs x29 (x_S x - 8784) (SP + 200) (x_S x) ST STU ltac:(lia)) as STM.
      assert (E18 : reg_get (ms_regs ms) 18 = Z_to_bv 64 (h_rows (hd x))) by exact Hs2.
      rewrite E18.
      apply evt_done. split.
      { unfold kept. cbn [ms_mem MS]. rewrite <- Em. split; [exact MU | exact WM]. }
      left. split; [rewrite Eok; first [reflexivity | exact Ef]|].
      unfold At_mallocSW1, at_after_admit, body, common, cur, slots, cslot, table, arrays.
      cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem MS].
      repeat match goal with |- _ /\ _ => split end.
      all: try (unfold w64, PC_MALLOC_SW1; reflexivity).
      all: try assumption.
      all: try (rewrite Eok; first [reflexivity | exact Ef]).
      all: try (unfold rg, PropExec.getr; cbn -[Z_to_bv w64]; first [exact Hgp | exact Htp | exact Hs0 | exact Hs9 | reflexivity]).
      all: try (unfold rg, PropExec.getr, w64, SPL, LLVM_FRAME; cbn -[Z_to_bv]; rewrite ?ESP; reflexivity).
      all: try (unfold SPL, LLVM_FRAME; rewrite <- ESP; first [exact FRa2 | exact Hslots | exact Hcs | exact HST | exact HWS]).
      all: try (unfold SPL, LLVM_FRAME; rewrite <- ESP; replace SP with (SP + 0) by lia; exact Hslots).
      all: try (unfold LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK; exact STM).
      all: try (unfold blk, CTRL_HEADAMP_ROW, CTRL_HEADAMP_BYTES, LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK, x_n;
                cbn [map]; first [exact Hrow | lia]).
      all: transitivity (Z_to_bv 64 ((bv_unsigned (Z_to_bv 64 (h_rows (hd x))) +
                                       Z.b2z (bv_unsigned (Z_to_bv 64 (h_rows (hd x))) <? 1))
                                       mod 18446744073709551616 * 34)); [reflexivity|].
      all: unfold w64, sw1_size; f_equal;
           rewrite unsigned_lit by lia; destruct (Z.ltb_spec (h_rows (hd x)) 1); cbn [Z.b2z];
           rewrite ?Z.mod_small by lia; lia.
    + destruct POST as (Hr0 & FRa2). subst x17.
      pose proof (fits_false_iff _ _ Ef) as Hnf.
      apply rw_C2_zero in FRa2.
      zstep. zstep. if_cases HC2; zify_cond HC2; [cbn [Z.b2z] in HC2; exfalso; lia|].
      zstep. zstep. if_cases HC3; zify_cond HC3; [exfalso; lia|].
      zstep. zstep. zstep. zstep. zstep. if_cases HC4; zify_cond HC4.
      { exfalso. cbn [firstn skipn] in HC4. rewrite !lbu_val in HC4 by lia. apply HC4. reflexivity. }
      eapply stk_release in ST; [ | exact FRa2 | lia ]. cbn [cells_size csize Nat.add] in ST.
      replace (SP + 198 + Z.of_nat 2) with (SP + 200) in ST by lia.
      pose proof (stk_merge rsegs x29 (x_S x - 8784) (SP + 200) (x_S x) ST STU ltac:(lia)) as STM.
      apply evt_done. split.
      { unfold kept. cbn [ms_mem MS]. rewrite <- Em. split; [exact MU | exact WM]. }
      right. split; [rewrite Eok; first [reflexivity | exact Ef]|].
      unfold At_raw. split; [| left; split; [reflexivity | rewrite Eok; first [reflexivity | exact Ef]]].
      unfold at_after_admit, body, common, cur, slots, cslot, table, arrays.
      cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem MS].
      repeat match goal with |- _ /\ _ => split end.
      all: try (unfold w64, PC_RAW_NOK; reflexivity).
      all: try assumption.
      all: try (unfold rg, PropExec.getr; cbn -[Z_to_bv w64]; first [exact Hgp | exact Htp | exact Hs0 | exact Hs9 | reflexivity]).
      all: try (unfold rg, PropExec.getr, w64, SPL, LLVM_FRAME; cbn -[Z_to_bv]; rewrite ?ESP; reflexivity).
      all: try (unfold SPL, LLVM_FRAME; rewrite <- ESP; first [exact Hslots | exact Hcs | exact HST | exact HWS]).
      all: try (unfold SPL, LLVM_FRAME; rewrite <- ESP; replace SP with (SP + 0) by lia; exact Hslots).
      all: try (unfold LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK; exact STM).
      all: try (unfold blk, CTRL_HEADAMP_ROW, CTRL_HEADAMP_BYTES, LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK, x_n;
                cbn [map]; first [exact Hrow | lia]).
Qed.

Theorem seg_admit_holds : reac_grant_alloc_fits_contract -> reac_grant_allocate_contract -> seg_admit.
Proof.
  intros FITS ALLOC. unfold seg_admit. intros x t ms H.
  assert (EQ : forall ms0, eqv_inv (fun ms' => kept x [] ms0 ms' /\
      (ok (x_pl x) = true /\ At_mallocSW1 x t ms' \/ ok (x_pl x) = false /\ At_raw x t PC_RAW_NOK ms'))).
  { intros ms0. apply eqv_and; [apply eqv_kept |].
    intros a b He [[Hok Ha] | [Hok Ha]]; [left | right]; split; try exact Hok.
    - exact (eqv_At_mallocSW1 x t a b He Ha).
    - exact (eqv_At_raw x t PC_RAW_NOK a b He Ha). }
  apply evt_canon; [apply EQ|].
  destruct H as (((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & Hpay & Hstk & Hinv & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                  Hsp & Hfr & Hal & Hlen & HSlt) & Hn & Hs0 & Hs9 & Hslots & Hcs & Htab & Harr & HH & HI1).
  rewrite canon_MS by exact Hsvc. unfold mkR_of.
  unfold w64, PC_ADMIT in Hpc. rewrite Hpc, Hrv, Hro.
  assert (E2 : reg_get (ms_regs ms) 2 = Z_to_bv 64 (SPL x)) by exact Hsp.
  rewrite E2. unfold slots, cslot in Hslots, Hcs. unfold SPL in *. unfold LLVM_FRAME in *.
  pose proof (hdr_ranges (x_pl x)) as (Ru & Rb & Ri & Rr & Rs).
  fold (hd x) in Ru, Rb, Ri, Rr, Rs.
  assert (Eok : ok (x_pl x) = fits (h_base (hd x)) (h_in (hd x))) by reflexivity.
  apply (evt_cut _ (fun ms' => ms_mem ms' = ms_mem ms /\ Mid x t ms')).
  - remember (x_S x - 592) as SP eqn:ESP.
    zstep. zstep. zstep. zstep.
    zstep. if_cases HC1; zify_cond HC1.
    + assert (Ef : fits (h_base (hd x)) (h_in (hd x)) = false).
      { apply fits_false. intros (Hw & _ & _).
        rewrite Z.mod_small in HC1 by lia. lia. }
      zstep. zstep. apply evt_done. split; [reflexivity|].
      mid_close ESP Hgp Htp Hs0 Hs9.
      all: unfold rg, PropExec.getr; cbn -[Z_to_bv w64]; rewrite Eok, Ef; reflexivity.
    + assert (Hw : 1 <= h_in (hd x) <= 40).
      { destruct (Z.eq_dec (h_in (hd x)) 0) as [E0|E0].
        - rewrite E0 in HC1. cbn in HC1. lia.
        - rewrite Z.mod_small in HC1 by lia. lia. }
      zstep. zstep. zstep. zstep. zstep. if_cases HC2; zify_cond HC2.
      * apply shl48_neg in HC2; [|lia].
        assert (Ef : fits (h_base (hd x)) (h_in (hd x)) = false) by (apply fits_false; lia).
        apply evt_done. split; [reflexivity|].
        mid_close ESP Hgp Htp Hs0 Hs9.
        all: unfold rg, PropExec.getr; cbn -[Z_to_bv w64]; rewrite Eok, Ef; reflexivity.
      * assert (HB : 0 <= h_base (hd x)).
        { apply Rs. destruct (Z_lt_le_dec (h_u16 (hd x)) 32768) as [L|L]; [exact L|].
          apply (shl48_neg (h_u16 (hd x)) Ru) in L. lia. }
        zstep. zstep. zstep. apply evt_done. split; [reflexivity|].
        mid_close ESP Hgp Htp Hs0 Hs9.
        all: unfold rg, PropExec.getr; cbn -[Z_to_bv w64]; rewrite Eok; unfold w64;
             first [rewrite slti49_ok' by lia | rewrite slti49_ok by lia]; reflexivity.
  - intros ms1 HP. cbv beta in HP. destruct HP as (Hm1 & HM).
    eapply evt_mono; [exact (admit_tail FITS ALLOC x t ms1 HM)|].
    intros ms2 HQ. cbv beta in HQ. destruct HQ as (Hk & Hq). split; [| exact Hq].
    unfold kept in *. rewrite Hm1 in Hk. exact Hk.
Qed.
