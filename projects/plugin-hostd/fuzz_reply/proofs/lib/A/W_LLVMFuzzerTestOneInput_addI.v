(* The placement / instance hypotheses of ARM_add (lib/A/W_LLVMFuzzerTestOneInput_add.v) proved at PI := PB_fr,
   RG := fr_globals, for an instance B satisfying AF0m's TfibSyms (the start-up table, lib/A/AF0m.v, whose ONE home is
   another branch; carried here by path).  Proofs from a scratch file (ZZaddHyps.v (sha256 e2dc655aa4cd; internal record),
   w8c rc=0, Print Assumptions primitives only), taken unchanged into the W8 tree by W8Entry-2; the measurement Eval
   and the scratch composition section are dropped (the composition is W_LLVMFuzzerTestOneInput_top.v's).
   What each lemma discharges: zz_HEV (HEV, ts_errno), zz_HZS (HZS, ts_zsh), zz_HGOBJ (HGOBJ at G_fr_c), zz_ROMPIN
   (ROMPIN: 19 owned read-only ranges, 408 bytes, each pinned by a Tfib_const_abs AV cell), zz_GSHV (GSHV at ad_G:
   every shadow-hull byte zero-shadow or a const shadow cell), zz_ERRL (errno_law), zz_OA_from_W2 (op_add's
   oa_spec_g from W2's pb_op_add_g with its closed premises discharged), zz_HOWN (G_fr_c's bytes are not owned). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_G W_LLVMFuzzerTestOneInput_latch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0l AF0m.
(* K0's caller-context tables (a working branch d7a13213c59, the generated tables' home; carried by path) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACk0.
(* AR_laws_x (YCbqG) at ARi0 (W_journal_x), the laws form W2's re-derived pb_op_add_g takes *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
Import ListNotations.
Open Scope Z_scope.

Section p.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* ================================================================ HEV *)
Lemma zz_HEV : forall B, TfibSyms B -> as_errno B = TFIB_ERRNO_A.
Proof. intros B TS. rewrite (@ts_errno B TS). reflexivity. Qed.

(* ================================================================ HZS *)
Lemma zz_HZS : forall B, TfibSyms B -> azs B (rg_s fr_RG) (4 * ASRC).
Proof.
  intros B TS. unfold azs. rewrite (@ts_zsh B TS).
  exists (0x5d88e0, 0x5d8a60 - 0x5d88e0). split.
  - unfold Tfib_zero_shadow. repeat (first [left; reflexivity | right]).
  - vm_compute. repeat split; first [reflexivity | discriminate | (let H := fresh in intro H; discriminate H)].
Qed.

(* ================================================================ HGOBJ (at G_fr := G_fr_c B, top.v's G_fr) *)
Lemma zz_HGOBJ : forall B a, inG G_fr_obj a -> inG (G_fr_c B) a.
Proof. intros B a Ha. eapply obj_c. exact Ha. Qed.

(* ================================================================ ROMPIN *)
Lemma zz_rom_range : forall a, in_rom segs a -> 0x10000 <= a < 0x9d000.
Proof.
  intros a (sg & Hin & Hw & Hr).
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)
     (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs))
    by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs sg Hin).
  rewrite Hw in H.
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; inversion H; subst; lia.
Qed.
Definition zz_romown : list (Z * Z) :=
  flat_map (fun r => if Z.max (fst r) 0x10000 <? Z.min (fst r + snd r) 0x9d000
                     then [(Z.max (fst r) 0x10000, Z.min (fst r + snd r) 0x9d000 - Z.max (fst r) 0x10000)] else [])
    Tfib_owned_static.
Lemma zz_romown_in : forall a r, In r Tfib_owned_static -> in_zr a r -> 0x10000 <= a < 0x9d000 -> inG zz_romown a.
Proof.
  intros a r Hr Hz Ha. unfold inG, zz_romown. apply Exists_exists.
  exists (Z.max (fst r) 0x10000, Z.min (fst r + snd r) 0x9d000 - Z.max (fst r) 0x10000).
  unfold in_zr in *. split.
  - apply in_flat_map. exists r. split; [exact Hr|].
    destruct (Z.max (fst r) 0x10000 <? Z.min (fst r + snd r) 0x9d000) eqn:E; [left; reflexivity|].
    apply Z.ltb_ge in E. lia.
  - cbn [fst snd]. lia.
Qed.
Definition zz_numcell (c : acell) : option (Z * nat * Z) :=
  match c with ACell (ANum z) w (AV (ANum v)) => Some (z, w, v) | _ => None end.
Lemma zz_numcell_ok : forall c z w v, zz_numcell c = Some (z, w, v) -> c = ACell (ANum z) w (AV (ANum v)).
Proof.
  intros [ca w cv] z w' v H. destruct ca; try (simpl in H; discriminate H).
  destruct cv as [e|mk vk]; [|simpl in H; discriminate H].
  destruct e; try (simpl in H; discriminate H). simpl in H. injection H as -> -> ->. reflexivity.
Qed.
Definition zz_cell_pin (a : Z) (c : acell) : bool :=
  match zz_numcell c with
  | Some (z, w, v) =>
      if (z <=? a) && (a <? z + Z.of_nat w) then
        match seg_rom segs (Z_to_bv 64 a) with
        | Some b => bv_unsigned b =? le_byte v w (Z.to_nat (a - z))
        | None => false
        end
      else false
  | None => false
  end.
Definition zz_pinb (a : Z) : bool := existsb (zz_cell_pin a) Tfib_const_abs.
Definition zz_bytes (G : list (Z * Z)) : list Z :=
  flat_map (fun r => map (fun i => fst r + Z.of_nat i) (seq 0 (Z.to_nat (snd r)))) G.
Lemma zz_pin_sound : forall B ly a, (forall ly, as_const B ly = Tfib_const ly) -> zz_pinb a = true ->
  exists c e, In c (as_const B ly) /\ c_val c = AV e /\
  aeval B ly (c_at c) <= a < aeval B ly (c_at c) + Z.of_nat (c_w c) /\
  Some (le_byte (aeval B ly e) (c_w c) (Z.to_nat (a - aeval B ly (c_at c)))) =
  option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Proof.
  intros B ly a HC H. unfold zz_pinb in H. apply existsb_exists in H as (c & Hin & Hc).
  unfold zz_cell_pin in Hc. destruct (zz_numcell c) as [[[z w] v]|] eqn:En; [|discriminate Hc].
  apply zz_numcell_ok in En. subst c.
  destruct ((z <=? a) && (a <? z + Z.of_nat w)) eqn:Eb; [|discriminate Hc].
  apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:Es; [|discriminate Hc].
  apply Z.eqb_eq in Hc.
  exists (ACell (ANum z) w (AV (ANum v))), (ANum v). cbn [c_at c_w c_val aeval].
  split; [rewrite HC; unfold Tfib_const; apply in_or_app; right; apply in_or_app; left; exact Hin|].
  split; [reflexivity|]. split; [lia|]. cbn [option_map]. rewrite Hc. reflexivity.
Qed.
Lemma zz_ROMPIN : forall B, TfibSyms B ->
  forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
Proof.
  intros B TS a Hr Ho. rewrite (@ts_owned B TS) in Ho.
  pose proof (zz_rom_range a Hr) as Ha.
  apply Exists_exists in Ho as (r & Hin & Hz).
  pose proof (zz_romown_in a r Hin Hz Ha) as HG.
  pose proof (rng_all_in zz_pinb zz_romown a ltac:(vm_compute; reflexivity) HG) as Hp.
  intros ly. exact (zz_pin_sound B ly a (@ts_const B TS) Hp).
Qed.

(* ================================================================ GSHV *)
Definition zz_avcell (c : acell) : option (Z * nat) :=
  match c with ACell (ANum z) w (AV _) => Some (z, w) | _ => None end.
Lemma zz_avcell_ok : forall c z w, zz_avcell c = Some (z, w) -> exists e, c = ACell (ANum z) w (AV e).
Proof.
  intros [ca w cv] z w' H. destruct ca; try (simpl in H; discriminate H).
  destruct cv as [e|mk vk]; [|simpl in H; discriminate H]. simpl in H. injection H as -> ->. exists e. reflexivity.
Qed.
Definition zz_visb (s : Z) : bool :=
  existsb (fun r => (shadow_of_addr SHADOW_OFF (fst r) <=? s) && (s <? shadow_of_addr SHADOW_OFF (fst r) + snd r / 8))
    Tfib_zero_shadow
  || existsb (fun c => match zz_avcell c with Some (z, w) => (z <=? s) && (s <? z + Z.of_nat w) | None => false end)
       (Tfib_const_abs ++ Tfib_const_shadow).
Lemma zz_vis_sound : forall B ly S rd s, TfibSyms B -> ARm B ly S rd -> zz_visb s = true -> rd s <> None.
Proof.
  intros B ly S rd s TS HM Hv. unfold zz_visb in Hv. apply orb_prop in Hv as [Hv|Hv].
  - apply existsb_exists in Hv as (r & Hin & Hb). apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    pose proof (am_zshadow _ _ _ _ HM) as HZ0. unfold zshadow_ok, zero_shadow_ranges in HZ0.
    rewrite (@ts_zsh B TS) in HZ0. apply Forall_inv_tail in HZ0.
    pose proof (proj1 (Forall_forall _ _) HZ0 r Hin) as Hr. unfold zero_shadow in Hr.
    specialize (Hr (s - shadow_of_addr SHADOW_OFF (fst r)) ltac:(lia)).
    replace (shadow_of_addr SHADOW_OFF (fst r) + (s - shadow_of_addr SHADOW_OFF (fst r))) with s in Hr by lia.
    rewrite Hr. discriminate.
  - apply existsb_exists in Hv as (c & Hin & Hb).
    destruct (zz_avcell c) as [[z w]|] eqn:Ec; [|discriminate Hb].
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (zz_avcell_ok c z w Ec) as (e & ->).
    pose proof (am_const _ _ _ _ HM) as HCH. rewrite (@ts_const B TS) in HCH.
    pose proof (proj1 (Forall_forall _ _) HCH (ACell (ANum z) w (AV e))
      ltac:(unfold Tfib_const; apply in_or_app; right; exact Hin)) as Hh.
    unfold cell_holds in Hh. cbn [c_at c_w c_val aeval] in Hh.
    specialize (Hh (Z.to_nat (s - z)) ltac:(lia)). rewrite Z2Nat.id in Hh by lia.
    replace (z + (s - z)) with s in Hh by lia. rewrite Hh. discriminate.
Qed.
Definition zz_hlo (r : Z * Z) : Z := shadow_addr (fst r) / 8 * 8.
Definition zz_hhi (r : Z * Z) : Z := shadow_addr (fst r + snd r - 1) / 8 * 8 + 8.
Definition zz_hull_ok (r : Z * Z) : bool :=
  forallb (fun i => zz_visb (zz_hlo r + Z.of_nat i)) (seq 0 (Z.to_nat (zz_hhi r - zz_hlo r))).
Definition zz_inb (G : list (Z * Z)) (x : Z) : bool := existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) G.
Lemma zz_inb_ok : forall G x, inG G x -> zz_inb G x = true.
Proof.
  intros G x H. unfold inG in H. apply Exists_exists in H as (r & Hr & Hz). unfold zz_inb. apply existsb_exists.
  exists r. split; [exact Hr|]. unfold in_zr in Hz. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma zz_GSHV : forall B, TfibSyms B ->
  forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG ad_G x) -> shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
  intros B TS ly S W mem md a n HAR Hn Hx. destruct HAR as (HM & _).
  pose proof (Hx a ltac:(lia)) as Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). unfold in_zr in Hz.
  assert (Hend : a + n <= fst r + snd r).
  { destruct (Z_le_gt_dec (a + n) (fst r + snd r)) as [H|H]; [exact H|]. exfalso.
    pose proof (Hx (fst r + snd r) ltac:(lia)) as Hb.
    assert (Hgap : forallb (fun r => negb (zz_inb ad_G (fst r + snd r))) ad_G = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hgap. specialize (Hgap r Hr). rewrite (zz_inb_ok _ _ Hb) in Hgap. discriminate Hgap. }
  assert (Hhull : forallb zz_hull_ok ad_G = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hhull. specialize (Hhull r Hr). unfold zz_hull_ok in Hhull. rewrite forallb_forall in Hhull.
  unfold shadow_hull_vis. intros s Hs.
  assert (Hlo : zz_hlo r <= s < zz_hhi r).
  { unfold zz_hlo, zz_hhi, shadow_addr in *.
    assert (D1 : fst r / 8 <= a / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : (a + n - 1) / 8 <= (fst r + snd r - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (M1 : (SHADOW_OFF + fst r / 8) / 8 <= (SHADOW_OFF + a / 8) / 8) by (apply Z.div_le_mono; lia).
    assert (M2 : (SHADOW_OFF + (a + n - 1) / 8) / 8 <= (SHADOW_OFF + (fst r + snd r - 1) / 8) / 8)
      by (apply Z.div_le_mono; lia).
    lia. }
  pose proof (Hhull (Z.to_nat (s - zz_hlo r)) ltac:(apply in_seq; lia)) as Hv.
  rewrite Z2Nat.id in Hv by lia. replace (zz_hlo r + (s - zz_hlo r)) with s in Hv by lia.
  exact (zz_vis_sound B ly S _ s TS HM Hv).
Qed.

(* ================================================================ ERRL (brief: callee / instance; decided here too) *)
Lemma zz_byte_some : forall (m : word -> option byte) a, seg_rom segs (Z_to_bv 64 a) <> None ->
  exists b, mbyte segs m a = Some b.
Proof.
  intros m a H. unfold mbyte. destruct (m (Z_to_bv 64 a)) as [b|]; [eauto|].
  destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [eauto | congruence].
Qed.
Lemma zz_bv_of_u : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as Hb.
  unfold bv_wrap, bv_modulus in *. cbn [Z.of_N] in *. change (2 ^ 8) with 256 in *. apply Z.mod_small. lia.
Qed.
Definition zz_v4 (v0 v1 v2 v3 : Z) : Z := v0 + 256 * (v1 + 256 * (v2 + 256 * v3)).
Lemma zz_le4 : forall v0 v1 v2 v3, 0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 ->
  le_byte (zz_v4 v0 v1 v2 v3) 4 0 = v0 /\ le_byte (zz_v4 v0 v1 v2 v3) 4 1 = v1 /\
  le_byte (zz_v4 v0 v1 v2 v3) 4 2 = v2 /\ le_byte (zz_v4 v0 v1 v2 v3) 4 3 = v3 /\
  0 <= zz_v4 v0 v1 v2 v3 < 2 ^ 32.
Proof.
  intros v0 v1 v2 v3 H0 H1 H2 H3. unfold le_byte.
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
  change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 3)) with 16777216.
  change (2 ^ 32) with 4294967296.
  assert (Hv : 0 <= zz_v4 v0 v1 v2 v3 < 4294967296) by (unfold zz_v4; lia).
  rewrite (Z.mod_small (zz_v4 v0 v1 v2 v3)) by exact Hv.
  split; [|split; [|split; [|split]]]; try exact Hv; unfold zz_v4; Z.div_mod_to_equations; lia.
Qed.
Lemma zz_ERRL : forall B, TfibSyms B -> errno_law B.
Proof.
  intros B TS ly S W mem md _. rewrite (zz_HEV B TS).
  assert (HS : forall j, 0 <= j < 8 -> seg_rom segs (Z_to_bv 64 (TFIB_ERRNO_A + j)) <> None).
  { intros j Hj.
    assert (Hb : forallb (fun i => match seg_rom segs (Z_to_bv 64 (TFIB_ERRNO_A + Z.of_nat i)) with
                                   Some _ => true | None => false end) (seq 0 8) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat j) ltac:(apply in_seq; lia)).
    rewrite Z2Nat.id in Hb by lia. destruct (seg_rom segs (Z_to_bv 64 (TFIB_ERRNO_A + j))); [discriminate | discriminate Hb]. }
  split.
  - destruct (zz_byte_some (arm W mem) (TFIB_ERRNO_A + 0) (HS 0 ltac:(lia))) as (b0 & E0).
    destruct (zz_byte_some (arm W mem) (TFIB_ERRNO_A + 1) (HS 1 ltac:(lia))) as (b1 & E1).
    destruct (zz_byte_some (arm W mem) (TFIB_ERRNO_A + 2) (HS 2 ltac:(lia))) as (b2 & E2).
    destruct (zz_byte_some (arm W mem) (TFIB_ERRNO_A + 3) (HS 3 ltac:(lia))) as (b3 & E3).
    pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
    pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
    unfold bv_modulus in R0, R1, R2, R3. cbn [Z.of_N] in R0, R1, R2, R3. change (2 ^ 8) with 256 in R0, R1, R2, R3.
    destruct (zz_le4 (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2) (bv_unsigned b3) R0 R1 R2 R3)
      as (L0 & L1 & L2 & L3 & Hv).
    exists (zz_v4 (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2) (bv_unsigned b3)). split; [|exact Hv].
    intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | lia].
    + change (Z.of_nat 0) with 0. rewrite E0. f_equal. rewrite <- (zz_bv_of_u b0) at 1. f_equal. symmetry. exact L0.
    + change (Z.of_nat 1) with 1. rewrite E1. f_equal. rewrite <- (zz_bv_of_u b1) at 1. f_equal. symmetry. exact L1.
    + change (Z.of_nat 2) with 2. rewrite E2. f_equal. rewrite <- (zz_bv_of_u b2) at 1. f_equal. symmetry. exact L2.
    + change (Z.of_nat 3) with 3. rewrite E3. f_equal. rewrite <- (zz_bv_of_u b3) at 1. f_equal. symmetry. exact L3.
  - intros i Hi. unfold arm. apply wr_of_seg. apply segwb_ok.
    apply (rng_all_in (segwb segs) [(TFIB_ERRNO_A, 4)]); [vm_compute; reflexivity|].
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* ================================================================ OA: W2's pb_op_add_g at PB_fr, its closed premises
   discharged; what is left is exactly the callee / law premises *)
Lemma zz_OA_from_W2 : forall (B : asyms) (MT : ameter_ops), TfibSyms B ->
  AR_laws_x segs B (ARi0 segs B) 0 -> PALib B -> ameter_laws MT -> forall MMAX, APARTIAL < MMAX ->
  amalloc_cf_rule_c segs B MT MMAX CTX_AMALLOC ->
  sr_spec_g B MT (BASE + AF_fr_source_reset) ->
  ra_spec_g B MT fr_globals CTX_AREALLOC (BASE + AF_fr_relay_add) ->
  oa_spec_g (PI := PB_fr) B MT (BASE + AF_fr_op_add).
Proof.
  intros B MT TS LX0 TL MLAW MMAX HMMAX AMA SR RA.
  refine (pb_op_add_g B MT LX0 TL MLAW MMAX HMMAX _ _ _ _ _ CTX_AMALLOC _ AMA SR CTX_AREALLOC _ RA).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. repeat split; first [left; discriminate | right; discriminate |
      left; let H := fresh in intro H; discriminate H | right; let H := fresh in intro H; discriminate H].
  - intros a Ha. split; [|split].
    + apply segin_ok. apply (rng_all_in (segin segs) [(rg_wake fr_globals + 4, 4)]); [vm_compute; reflexivity|].
      apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
    + rewrite (@ts_owned B TS). intros Hex.
      exact (ad_apart_ok (rg_wake fr_globals + 4) 4 Tfib_owned_static ltac:(vm_compute; reflexivity) a Hex ltac:(lia)).
    + rewrite (@ts_errno B TS). cbn [fr_globals rg_wake] in Ha. unfold TFIB_ERRNO. lia.
  (* HCTX_oa_malloc: op_add's malloc is K0's malloc row [0x84fdc] (W2's CTX split, 16113e32f61) *)
  - assert (E : [BASE + AF_fr_op_add + 0xcc] = [0x84fdc]) by (vm_compute; reflexivity).
    rewrite E. unfold CTX_AMALLOC. vm_compute. repeat (first [left; reflexivity | right]).
  (* HCTXRA: op_add's call of relay_add is K0's realloc row [0x82a9c; 0x85018] (StartupTrace's ACk0.v) *)
  - assert (E : [BASE + AF_fr_relay_add + 332; BASE + AF_fr_op_add + 264] = [0x82a9c; 0x85018])
      by (vm_compute; reflexivity).
    rewrite E. unfold CTX_AREALLOC. cbn [In]. right; left; reflexivity.
Qed.
(* top.v's HOWN (needed for HG at G_fr_c B): G_fr_c's bytes are outside Tfib_owned_static *)
Lemma zz_HOWN : forall B, TfibSyms B -> forall a, inG (G_fr_c B) a -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
  intros B TS a Ha. rewrite (@ts_owned B TS). rewrite (G_fr_c_val B (zz_HEV B TS)) in Ha. intros Hex.
  assert (Hb : forallb (fun r => ad_apart (fst r) (snd r) Tfib_owned_static) (G_fr_obj ++ [(TFIB_ERRNO_A, 4)]) = true)
    by (vm_compute; reflexivity).
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). rewrite forallb_forall in Hb.
  exact (ad_apart_ok _ _ _ (Hb r Hr) a Hex Hz).
Qed.
(* QMm W0' (a Theorem Labs lane): gx_ok's kept clause at G_fr_c B: no byte of G is a kept byte (AF0m's Tfib_kept: the non-owned
   RELRO and part 3c's five read-only read ranges). This vm_compute IS a Theorem Labs lane's check that no concrete G meets as_kept. *)
Lemma zz_HKEPT : forall B, TfibSyms B -> forall a, inG (G_fr_c B) a -> ~ Exists (in_zr a) (as_kept B).
Proof.
  intros B TS a Ha. rewrite (@ts_kept B TS). rewrite (G_fr_c_val B (zz_HEV B TS)) in Ha. intros Hex.
  assert (Hb : forallb (fun r => ad_apart (fst r) (snd r) Tfib_kept) (G_fr_obj ++ [(TFIB_ERRNO_A, 4)]) = true)
    by (vm_compute; reflexivity).
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). rewrite forallb_forall in Hb.
  exact (ad_apart_ok _ _ _ (Hb r Hr) a Hex Hz).
Qed.
End p.
