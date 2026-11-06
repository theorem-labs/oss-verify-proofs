From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_family_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_scd.
Import ListNotations.
Open Scope Z_scope.

Lemma d01_rd : forall m p inp i, bytes_at rsegs m p inp -> 0 <= i < nlen inp ->
  ov_read_bytes rsegs m (wa (p + i)) 1 = Some [RcIdentModel.nthb inp (Z.to_nat i)].
Proof.
  intros m p inp i H Hi. unfold nlen in Hi.
  rewrite (bytes_at_read rsegs m p inp i 1 H) by lia.
  f_equal. apply reac_box_family_of.famof_firstn1. lia.
Qed.

Lemma d01_zero : forall inp j, 0 <= j -> nlen inp <= cT inp + j -> tb inp j = 0.
Proof.
  intros inp j Hj H. pose proof (rec_c_range inp (nrecn inp)) as Hc. unfold cT in *.
  unfold tb, inb, RcIdentModel.bz, RcIdentModel.nthb, cT. unfold nlen in *.
  rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma d01_ne : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> x <> k ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 k) = false.
Proof. intros x k Hx Hk H. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. exact H. Qed.

Lemma d01_eq : forall x k, x = k -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 k) = true.
Proof. intros x k ->. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma d01_ov1 : forall segs m y, ov_read_bytes segs m y 1 = match mrd segs m y with Some b => Some [b] | None => None end.
Proof. intros segs m y. rewrite ov_rdn, rdn_unfold. destruct (mrd segs m y); reflexivity. Qed.

Lemma d01_rdw : forall m a v x b, ov_read_bytes rsegs m (wa x) 1 = Some [b] -> 0 <= a ->
  a + 8 <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> x < a \/ a + 8 <= x ->
  ov_read_bytes rsegs (write_to_mem m (Z_to_bv 64 a) (le8 v)) (wa x) 1 = Some [b].
Proof.
  intros m a v x b H Ha Hl Hx Hd. rewrite d01_ov1 in *. unfold mrd in *.
  assert (Hu : bv_unsigned (wa x) = x) by (unfold wa; apply MState.unsigned_lit; lia).
  change (Z_to_bv 64 a) with (wa a).
  rewrite write_to_mem_spec by (rewrite ?length_le8; lia). rewrite Hu, length_le8.
  destruct (Z.leb_spec a x); destruct (Z.ltb_spec x (a + Z.of_nat 8)); cbn [andb]; try lia; exact H.
Qed.

Lemma d01_af2 : forall x, 0 <= x < 256 -> x - x * 205 / 8192 * 40 = x mod 40.
Proof.
  intros x Hx.
  pose proof (z_all_spec (fun x => (x - x * 205 / 8192 * 40) =? x mod 40) 256 0 ltac:(vm_compute; reflexivity) x
    ltac:(lia)) as H.
  cbv beta in H. apply Z.eqb_eq in H. exact H.
Qed.

Lemma d01_m40 : forall b : byte,
  Z_to_bv 64 (bv_unsigned (zxb b) - bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned
    (Z_to_bv 64 (bv_unsigned (zxb b) * 205)) ≫ 13)) * 40))) = Z_to_bv 64 (bv_unsigned b mod 40).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. rewrite (MState.unsigned_lit (bv_unsigned b)) by lia.
  rewrite (MState.unsigned_lit (bv_unsigned b * 205)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 13) with 8192.
  rewrite (MState.unsigned_lit (bv_unsigned b * 205 / 8192)) by (Z.div_mod_to_equations; lia).
  rewrite (MState.unsigned_lit (bv_unsigned b * 205 / 8192 * 40)) by (Z.div_mod_to_equations; lia).
  f_equal. apply d01_af2. exact R.
Qed.

Lemma d01_land : forall b : byte, forall n, 0 <= n ->
  Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) (Z.ones n)) = Z_to_bv 64 (bv_unsigned b mod 2 ^ n).
Proof.
  intros b n Hn. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. rewrite (MState.unsigned_lit (bv_unsigned b)) by lia. rewrite Z.land_ones by exact Hn. reflexivity.
Qed.

Lemma d01_m16 : forall b : byte, Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 15) = Z_to_bv 64 (bv_unsigned b mod 16).
Proof. intros b. exact (d01_land b 4 ltac:(lia)). Qed.
Lemma d01_m32 : forall b : byte, Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 31) = Z_to_bv 64 (bv_unsigned b mod 32).
Proof. intros b. exact (d01_land b 5 ltac:(lia)). Qed.
Lemma d01_m64 : forall b : byte, Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 63) = Z_to_bv 64 (bv_unsigned b mod 64).
Proof. intros b. exact (d01_land b 6 ltac:(lia)). Qed.

Ltac d01_getr :=
  repeat match goal with
  | |- context [getr ?R ?r] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (getr R r) with (Sem.reg_get R r)
  end.

Ltac d01_z :=
  unfold t_fam_raw, t_in, t_out, t_row, t_cap_fw, t_cap_ver, t_cap_name, t_cap_tok, t_cap_disp;
  rewrite d01_zero by lia; reflexivity.

Ltac d01_val :=
  first [ reflexivity
        | etransitivity; [apply d01_m16 | reflexivity]
        | etransitivity; [apply d01_m32 | reflexivity]
        | etransitivity; [apply d01_m40 | reflexivity]
        | etransitivity; [apply d01_m64 | reflexivity]
        | d01_z ].

Ltac d01_reg := d01_getr; simp_regs; d01_val.

Ltac d01_mem := f_equal; f_equal; d01_val.

Ltac d01_splits :=
  lazymatch goal with
  | |- _ /\ _ => split; [d01_reg | d01_splits]
  | _ => d01_reg
  end.

Ltac d01_rds mem g Hin E k :=
  let H := fresh "HR" in
  assert (H : ov_read_bytes rsegs mem (wa (g_p g + cT (g_in g) + k)) 1 =
              Some [RcIdentModel.nthb (g_in g) (Z.to_nat (cT (g_in g) + k))])
    by (rewrite <- Z.add_assoc; apply d01_rd; [exact Hin | lia]).

Ltac d01_tr :=
  repeat match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m (Z_to_bv 64 ?a) (le8 ?v)) _) =>
      match goal with H : ov_read_bytes rsegs m (wa _) 1 = Some _ |- _ =>
        apply (d01_rdw m a v) in H; [| lia | lia | lia | lia] end
  end.

Ltac d01_brk :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      match goal with
      | |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?k)] =>
          first [ rewrite (d01_ne x k) by lia | rewrite (d01_eq x k) by lia ]
      end
  end.

Ltac d01_go :=
  repeat (d01_tr;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 79252) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => d01_brk; cbv beta iota delta [negb]
    end).

Ltac d01_fin :=
  apply Exec.evt_done; do 3 eexists; split; [reflexivity|];
  split; [reflexivity|]; split; [d01_mem|]; d01_splits.

Section D01.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Definition d01_K (g : ghost) (regs : bvmap 5 word) (mem : word -> option byte)
    (R : bvmap 5 word) (pc' : word) (mem' : word -> option byte) : Prop :=
  pc' = Z_to_bv 64 0x13594 /\
  mem' = write_to_mem mem (wa (fsp g + 40)) (le8 (Z_to_bv 64 (t_cap_disp (g_in g)))) /\
  getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
  getr R 8 = Z_to_bv 64 (t_fam_raw (g_in g)) /\ getr R 9 = Z_to_bv 64 (t_in (g_in g)) /\
  getr R 18 = Z_to_bv 64 (t_out (g_in g)) /\ getr R 19 = Z_to_bv 64 (t_row (g_in g)) /\
  getr R 24 = Z_to_bv 64 (t_cap_name (g_in g)) /\ getr R 25 = Z_to_bv 64 (t_cap_tok (g_in g)) /\
  getr R 22 = Z_to_bv 64 (t_cap_fw (g_in g)) /\ getr R 21 = Z_to_bv 64 (t_cap_ver (g_in g)) /\
  getr R 27 = Z_to_bv 64 (tb (g_in g) 9) /\ getr R 20 = Z_to_bv 64 (tb (g_in g) 10).

Lemma seg_D01 :
  Hcut B APIf ra (Inv_K13594 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13544 B APIf ra empty).
Proof.
  intros H594 g c Hc.
  destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HCUR & HTID & HP7).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwr).
  destruct (sc_input B APIf ra empty FF g _ _ L A regs mem md HF HP) as (Hin & Hp0 & Hpn).
  destruct (sc_fr_facts B APIf ra empty FF g _ _ L A regs mem md HF)
    as (Hro & _ & Hfsp & HSK & HS47 & Ef & Hsp).
  pose proof alloc_ceiling_val as Hc.
  destruct HCUR as (Hc0 & H20 & H26).
  pose proof HGV as (Hn26 & _).
  assert (Hgn : g_n g = nlen (g_in g)) by reflexivity.
  assert (HS : store_ok rsegs mem (wa (fsp g + 40)) 8 = true).
  { assert (W : wr_at rsegs mem (fsp g + 40) 8).
    { split; [lia|]. split; [lia|]. intros i Hi.
      pose proof (Hwr (fsp g + 40 + i) ltac:(unfold SLOT_K, SLOT_STACK; lia)) as X.
      unfold writable_at in X. rewrite (sc_segs B APIf ra empty FF) in X. exact X. }
    pose proof (wr_at_store_ok rsegs mem (fsp g + 40) 8 0 8 W ltac:(lia) ltac:(lia)) as X.
    rewrite Z.add_0_r in X. exact X. }
  apply (sc_run B APIf ra empty FF regs (Z_to_bv 64 0x13544) mem md L A (d01_K g regs mem) _ HMR).
  - unfold rmk, d01_K. rewrite Hsp, H20, H26.
    assert (Hcases : g_n g - cT (g_in g) <= 10 \/ 11 <= g_n g - cT (g_in g)) by lia.
    destruct Hcases as [E|E].
    + assert (Hk : g_n g - cT (g_in g) = 0 \/ g_n g - cT (g_in g) = 1 \/ g_n g - cT (g_in g) = 2 \/
                   g_n g - cT (g_in g) = 3 \/ g_n g - cT (g_in g) = 4 \/ g_n g - cT (g_in g) = 5 \/
                   g_n g - cT (g_in g) = 6 \/ g_n g - cT (g_in g) = 7 \/ g_n g - cT (g_in g) = 8 \/
                   g_n g - cT (g_in g) = 9 \/ g_n g - cT (g_in g) = 10) by lia.
      clear E.
      destruct Hk as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]];
        try d01_rds mem g Hin E 0; try d01_rds mem g Hin E 1; try d01_rds mem g Hin E 2;
        try d01_rds mem g Hin E 3; try d01_rds mem g Hin E 4; try d01_rds mem g Hin E 5;
        try d01_rds mem g Hin E 6; try d01_rds mem g Hin E 7; try d01_rds mem g Hin E 8;
        try d01_rds mem g Hin E 9.
      all: d01_go; d01_fin.
    + d01_rds mem g Hin E 0. d01_rds mem g Hin E 1. d01_rds mem g Hin E 2. d01_rds mem g Hin E 3.
      d01_rds mem g Hin E 4. d01_rds mem g Hin E 5. d01_rds mem g Hin E 6. d01_rds mem g Hin E 7.
      d01_rds mem g Hin E 8. d01_rds mem g Hin E 9. d01_rds mem g Hin E 10.
      d01_go. d01_fin.
  - intros R pc' mem' regs' (-> & -> & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E24 & E25 & E22 & E21 & E27 & E20') Hg.
    apply H594.
    assert (Hl8 : forall v : word, Z.of_nat (length (le8 v)) = 8) by (intros v; rewrite length_le8; reflexivity).
    set (v := le8 (Z_to_bv 64 (t_cap_disp (g_in g)))) in *.
    assert (HM' : munch [(g_S g - SLOT_K, g_S g - 104)] mem (write_to_mem mem (wa (fsp g + 40)) v)).
    { apply munch_write; [apply munch_refl | lia | unfold v; rewrite Hl8; lia |].
      unfold v. rewrite Hl8. cbn [inside]. left. unfold SLOT_K, SLOT_STACK. lia. }
    assert (HW' : wmono rsegs mem (write_to_mem mem (wa (fsp g + 40)) v)) by (apply wmono_write, wmono_refl).
    apply (sc_cut B APIf ra empty g _ _ _ _ L A regs' _ md); [| exact HP |].
    + apply (sc_FR_regs B APIf ra empty g _ _ L A regs regs' _ md); [| rewrite Hg; assumption ..].
      exact (sc_FR_frame B APIf ra empty FF g _ _ L A regs mem md _ HF HP HM' HW').
    + destruct HTID as (HG16 & HID).
      assert (Hot : forall a bs, bytes_at rsegs mem a bs -> a + Z.of_nat (length bs) <= fsp g + 40 \/ fsp g + 48 <= a ->
                      bytes_at rsegs (write_to_mem mem (wa (fsp g + 40)) v) a bs).
      { intros a bs Hb Hd. apply bytes_at_write_other; [exact Hb | lia | unfold v; rewrite Hl8; lia |].
        unfold v; rewrite Hl8. lia. }
      unfold D594, TL, TLr, TID, G16, IDb, q64, spk in *.
      rewrite !Hg.
      split; [split; [apply Hot; [exact HG16 | rewrite length_le8; lia] |
                      apply Hot; [exact HID | rewrite rec_id_length; unfold RcIdentModel.ID_SIZE; lia]]|].
      split; [split; [exact E8|] |].
      { split; [exact E9|]. split; [exact E18|]. split; [exact E19|]. split; [exact E24|]. split; [exact E25|].
        apply bytes_at_write_same; [lia | unfold v; rewrite Hl8; lia]. }
      split; [exact E22|]. split; [exact E21|]. split; [exact E27|]. exact E20'.
Qed.

End D01.
