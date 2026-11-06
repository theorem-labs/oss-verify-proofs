(* The per-call invariant of the cf driver loop (lib/A/AD1w_cf.v fr_LI = 0 <= ci <= 4 /\ W8's fr_gi) against the two
   statements AD1w_cf.v names for it: fr_lib_inv_stable (it survives what the driver does between calls) and
   fr_lib_inv_init (it holds at the first call).  Both are proved here, at fr_gi's writability text (W8's ruling G4,
   a working branch ec4dd616ed1 W_LLVMFuzzerTestOneInput_cut.v:148).
   - fr_lib_inv_stable_ok: every conjunct of fr_gi is carried through W_rep.v's frame lemmas (akept_*, *_kept): the
     globals' bytes are G_fr_c B's, the table's and g_out's are fr_FP's (ACfn_cf.v), read through g_src / g_out /
     g_capout with W_frame.rdword_of_val_mem.  That reading needs the blocks' addresses inside the address space and
     the table's nonzero: AD1w_cf.v's premise fr_blk_ok.  Without it the statement is false: fr_lib_inv_stable_v0_false
     below, a table at a live block whose address is 0 (g_src reads 0, so fr_FP drops the table's range).
   - fr_lib_inv_init_ok: the start-up values (vm_compute on the image's seg_rom: every .bss byte of G_fr_obj reads 0,
     g_client / g_listen / g_wake read 0xff) give every value conjunct; errno's four bytes (as_errno B = TFIB_ERRNO_A)
     are image bytes, so they read and are writable in every memory (c_glob_wr). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfNames YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G ACfn_cf AD1w_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ bytes *)
(* n bytes read v, little-endian (W_frame.v val_mem_of_rd32 at any width) *)
Lemma val_mem_of_view : forall segs H mem a n v,
  (forall k, (k < n)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v n k)) ->
  val_mem segs (mrestrict H mem) a n v.
Proof.
  intros segs H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
  destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
  change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma le_byte_0 : forall n k, le_byte 0 n k = 0.
Proof. intros n k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma le_byte4 : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  forall k, (k < 4)%nat -> le_byte (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) 4 k = nth k [b0; b1; b2; b3] 0.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3 k Hk. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
  rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.mod_small _ 4294967296) by lia.
  destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth];
  [change (2 ^ (8 * Z.of_nat 0)) with 1 | change (2 ^ (8 * Z.of_nat 1)) with 256
  | change (2 ^ (8 * Z.of_nat 2)) with 65536 | change (2 ^ (8 * Z.of_nat 3)) with 16777216]; lia.
Qed.
Lemma le_bytes4_range : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  0 <= b0 + 256 * (b1 + 256 * (b2 + 256 * b3)) < 2 ^ 32.
Proof. intros b0 b1 b2 b3 H0 H1 H2 H3. lia. Qed.

(* the image's start-up value of a byte: the segment byte, or 0 where the image has none *)
Definition fr_img (a : Z) : Z := match seg_rom tfibsegs (Z_to_bv 64 a) with Some b => bv_unsigned b | None => 0 end.
(* the n bytes at a lie in G_fr_obj and their start-up values read v *)
Definition fr_cellb (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => inGb G_fr_obj (a + Z.of_nat k) && (fr_img (a + Z.of_nat k) =? le_byte v n k)) (seq 0 n).

(* ------------------------------------------------------------------ the counterexample's state *)
(* fr_lib_inv_stable_v0_false: one live block of ATABLE bytes at PNull's address 0, every byte present, g_capsrc = 16
   (the relay holds the table there with no entry), g_client and g_wake[1] = 0xffffffff, every other byte 0; after
   the step the table's byte 5 is gone and nothing else changed. *)
Definition cx_ly : alayout := ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0).
Definition cx_S : astate :=
  mkA [] false [] [mkChunk PNull ATABLE CAllocated] [] [] 0 (mkQC [] 0) (mkQC [] 0) (mkFS [] []) [] false 0.
Lemma cx_Hoff : H_off_segments tfibsegs (fun _ => false).
Proof. intros a Ha. discriminate. Qed.
Definition cx_W : world tfibsegs := mkW tfibsegs (fun _ => false) [] cx_Hoff (Forall_nil _) (fun _ _ => eq_refl).
Definition cx_val (a : Z) : Z :=
  if a =? rg_capsrc fr_globals then 16
  else if (rg_client fr_globals <=? a) && (a <? rg_client fr_globals + 4) then 255
  else if (rg_wake fr_globals + 4 <=? a) && (a <? rg_wake fr_globals + 8) then 255 else 0.
Definition cx_mem : word -> option byte := fun w => Some (Z_to_bv 8 (cx_val (bv_unsigned w))).
Definition cx_mem' : word -> option byte := fun w => if bv_unsigned w =? 5 then None else cx_mem w.
Lemma cx_vm : forall a n v,
  forallb (fun k => cx_val (bv_unsigned (Z_to_bv 64 (a + Z.of_nat k))) =? le_byte v n k) (seq 0 n) = true ->
  val_mem tfibsegs (mrestrict (w_H cx_W) cx_mem) a n v.
Proof.
  intros a n v Hb k Hk. rewrite forallb_forall in Hb.
  assert (Hs : In k (seq 0 n)) by (apply in_seq; lia).
  pose proof (Hb k Hs) as Hv. apply Z.eqb_eq in Hv.
  unfold mbyte, mrestrict, cx_mem, cx_W. cbn [w_H]. rewrite Hv. reflexivity.
Qed.
Lemma cx_wr : forall a, writable_at tfibsegs (mrestrict (w_H cx_W) cx_mem) a.
Proof. intros a. unfold writable_at, wview, mrestrict, cx_mem, cx_W. cbn [w_H]. discriminate. Qed.
Lemma cx_garr8 : forall a l,
  forallb (fun j => (cx_val (bv_unsigned (Z_to_bv 64 (a + Z.of_nat j + Z.of_nat 0))) =? le_byte (nth j l 0) 1 0) &&
    (0 <=? nth j l 0) && (nth j l 0 <? 256)) (seq 0 (length l)) = true ->
  garr8 tfibsegs (mrestrict (w_H cx_W) cx_mem) a l.
Proof.
  intros a l Hb j Hj. rewrite forallb_forall in Hb.
  assert (Hs : In j (seq 0 (length l))) by (apply in_seq; lia).
  pose proof (Hb j Hs) as Hv. apply andb_prop in Hv as [Hv H2]. apply andb_prop in Hv as [Hv H1].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. split; [|lia].
  apply cx_vm. cbn [seq forallb]. rewrite Hv. reflexivity.
Qed.

Section inv.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable LIBROOM : astate -> Prop.
Variable NP : astate -> Prop.
Local Notation segs := tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Notation GF := (G_fr_c B).

(* ------------------------------------------------------------------ the footprint *)
Lemma fp_table : forall regs ly S (W : world segs) mem T a,
  rdword (aview segs (w_H W) mem) (rg_src fr_globals) = Some T -> T <> 0 -> T <= a < T + ATABLE ->
  inFP (fr_FP regs ly S W mem) a.
Proof.
  intros regs ly S W mem T a Hr Hz Ha. unfold fr_FP. cbv zeta. rewrite Hr.
  rewrite (proj2 (Z.eqb_neq T 0) Hz).
  exists (T, T + ATABLE). split; [apply in_or_app; left; left; reflexivity | exact Ha].
Qed.
Lemma fp_out : forall regs ly S (W : world segs) mem o c a,
  rdword (aview segs (w_H W) mem) (rg_out fr_globals) = Some o ->
  rdword (aview segs (w_H W) mem) (rg_capout fr_globals) = Some c -> c <> 0 -> o <= a < o + c ->
  inFP (fr_FP regs ly S W mem) a.
Proof.
  intros regs ly S W mem o c a Ho Hc Hz Ha. unfold fr_FP. cbv zeta. rewrite Ho, Hc.
  rewrite (proj2 (Z.eqb_neq c 0) Hz).
  exists (o, o + c). split; [apply in_or_app; right; left; reflexivity | exact Ha].
Qed.

(* ------------------------------------------------------------------ stability *)
Local Ltac kg KG := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; try (cbn [fst snd] in Hx); eapply KG; [|exact Hx]; vm_compute; reflexivity.

Theorem fr_lib_inv_stable_ok : fr_lib_inv_stable B.
Proof.
  intros ci0 regs ly S W mem ly' S' W' mem' [Hci GI] HBLK KEEP LIVE.
  assert (K : forall a, inG GF a \/ inFP (fr_FP regs ly S W mem) a -> abyte_kept (PI := PB_fr) W mem W' mem' a)
    by (intros a Ha; destruct (KEEP a Ha) as (E & _ & Wr); exact (conj E Wr)).
  assert (KG : forall lo hi, rng_inb lo (hi - lo) G_fr_obj = true -> forall a, lo <= a < hi ->
    abyte_kept (PI := PB_fr) W mem W' mem' a).
  { intros lo hi Hb a Ha. apply K. left. apply (obj_c B). apply (rng_cover lo (hi - lo) G_fr_obj Hb). lia. }
  split; [exact Hci|].
  destruct GI as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  split; [intros a Ha; exact (proj2 (proj2 (KEEP a (or_introl Ha))) (G1 a Ha))|].
  split.
  { intros i Hi. destruct (G2 i Hi) as (Hg & Hw).
    assert (KS : forall x, rg_s fr_RG + ASRC * Z.of_nat i <= x < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
      abyte_kept (PI := PB_fr) W mem W' mem' x).
    { intros x Hx. apply (KG (rg_s fr_RG) (rg_s fr_RG + 4 * ASRC)); [vm_compute; reflexivity|].
      clear -Hi Hx. unfold ASRC in *. lia. }
    split.
    - apply (akept_garr8 (PI := PB_fr) W mem); [|exact Hg]. intros x Hx. apply KS.
      clear -Hx. rewrite repeat_length in Hx. unfold ASRC in *. lia.
    - apply (akept_awr (PI := PB_fr) W mem); [exact KS | exact Hw]. }
  split.
  { destruct G3 as (T & [(HT & _ & E) | A]).
    - exists T. left. split; [exact HT|]. split; [reflexivity|].
      destruct E as (E1 & E2 & E3 & E4 & E5 & E6).
      split; [apply (akept_vm (PI := PB_fr) W mem); [kg KG | exact E1]|].
      split; [apply (akept_awr (PI := PB_fr) W mem); [kg KG | exact E2]|].
      split; [apply (akept_vm (PI := PB_fr) W mem); [kg KG | exact E3]|].
      split; [apply (akept_awr (PI := PB_fr) W mem); [kg KG | exact E4]|].
      split; [apply (akept_vm (PI := PB_fr) W mem); [kg KG | exact E5]|].
      apply (akept_awr (PI := PB_fr) W mem); [kg KG | exact E6].
    - exists T. right.
      pose proof A as (A1 & _ & _ & _ & _ & _ & _ & A8 & _).
      assert (Hrd : rdword (aview segs (w_H W) mem) (rg_src fr_globals) = Some T /\ T <> 0).
      { destruct (HBLK T ATABLE A8) as (HT0 & HT1). split; [|lia].
        apply (W_frame.rdword_of_val_mem segs); [exact A1|]. clear -HT0 HT1. unfold ATABLE in HT1. lia. }
      apply (arelay_at_kept (PI := PB_fr) B fr_RG ly S W mem); [exact A | |].
      + intros r Hr. cbn [arelay_fp concat map In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; [kg KG | kg KG | kg KG|].
        intros a Ha. cbn [fst snd] in Ha. apply K. right.
        exact (fp_table regs ly S W mem T a (proj1 Hrd) (proj2 Hrd) Ha).
      + intros b Hb. cbn [arelay_blks concat map In] in Hb. destruct Hb as [<-|[]]. exact (LIVE _ A8). }
  split.
  { destruct G4 as (c & O & mx & cap & out & Ho). exists c, O, mx, cap, out.
    assert (Hblk : cap <> 0 -> 0 < cap /\ In (out, cap) (ablocks B ly S)).
    { intros Hc. pose proof Ho as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & _ & H26).
      destruct H26 as [(E & _) | (Hc1 & _ & Hin & _)]; [contradiction | exact (conj Hc1 Hin)]. }
    assert (Kout : cap <> 0 -> forall a, out <= a < out + cap -> abyte_kept (PI := PB_fr) W mem W' mem' a).
    { intros Hc a Ha.
      pose proof Ho as (_ & _ & _ & _ & H5 & _ & H7 & _).
      destruct (Hblk Hc) as (Hc0 & Hin).
      destruct (HBLK out cap Hin) as (Ho0 & Ho1).
      apply K. right. apply (fp_out regs ly S W mem out cap a); [ | | exact Hc | exact Ha].
      - apply (W_frame.rdword_of_val_mem segs); [exact H7 | lia].
      - apply (W_frame.rdword_of_val_mem segs); [exact H5 | lia]. }
    apply (aout_at_kept (PI := PB_fr) B fr_RG ly S W mem); [exact Ho | |].
    - intros r Hr. unfold aout_fp in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]];
        [kg KG | kg KG | kg KG | kg KG | kg KG | kg KG | kg KG | kg KG | |].
      + intros a Ha. cbn [fst snd] in Ha. apply K. left. apply (err_c B). exact Ha.
      + revert Hr. destruct (Z.eqb_spec cap 0) as [_|Hc]; intros Hr; [destruct Hr|].
        destruct Hr as [<-|[]]. intros a Ha. cbn [fst snd] in Ha. exact (Kout Hc a Ha).
    - intros b Hb. unfold aout_blks in Hb. revert Hb.
      destruct (Z.eqb_spec cap 0) as [_|Hc]; intros Hb; [destruct Hb|].
      destruct Hb as [<-|[]]. exact (LIVE _ (proj2 (Hblk Hc))). }
  split; [destruct G5 as (gn & Hg); exists gn; apply (agone_at_kept (PI := PB_fr) fr_RG W mem);
    [exact Hg | intros r [<-|[]]; kg KG]|].
  split; [apply (alock_at_kept (PI := PB_fr) fr_RG W mem); [exact G6 | intros r [<-|[]]; kg KG]|].
  split; [apply (awake_at_kept (PI := PB_fr) fr_RG W mem); [exact G7 | intros r [<-|[]]; kg KG]|].
  split; [apply (akept_vm (PI := PB_fr) W mem); [kg KG | exact G8]|].
  split; [destruct G9 as (lst & Hl); exists lst; apply (akept_vm (PI := PB_fr) W mem); [kg KG | exact Hl]|].
  intros i Hi. apply (proj2 (KG AG_LISTEN (AG_LISTEN + 4) ltac:(vm_compute; reflexivity) (AG_LISTEN + i) ltac:(lia))).
  exact (G10 i Hi).
Qed.

(* ------------------------------------------------------------------ the first call *)
Theorem fr_lib_inv_init_ok : fr_lib_inv_init B.
Proof.
  intros HEV ly S W mem init P1 P2.
  assert (VIEW : forall a, inG G_fr_obj a -> aview segs (w_H W) mem a = Some (fr_img a)).
  { intros a Ha. rewrite (proj1 (P1 a Ha)). f_equal. unfold fr_img.
    destruct (P2 a Ha) as [E2 | (E2 & E3)].
    - revert E2. destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; cbn [option_map]; congruence.
    - rewrite E2. exact E3. }
  assert (CELL : forall a n v, fr_cellb a n v = true -> val_mem segs (rd W mem) a n v).
  { intros a n v Hb. apply val_mem_of_view. intros k Hk. unfold fr_cellb in Hb. rewrite forallb_forall in Hb.
    assert (Hs : In k (seq 0 n)) by (apply in_seq; lia).
    destruct (andb_prop _ _ (Hb k Hs)) as [Hin Hv]. apply inGb_spec in Hin. apply Z.eqb_eq in Hv.
    rewrite (VIEW _ Hin), Hv. reflexivity. }
  assert (WR : forall lo n, rng_inb lo n G_fr_obj = true -> awr (PI := PB_fr) W mem lo n).
  { intros lo n Hb i Hi. exact (proj2 (P1 (lo + i) (rng_cover lo n G_fr_obj Hb (lo + i) ltac:(lia)))). }
  split; [lia|].
  split; [intros a Ha; exact (c_glob_wr B HEV (w_H W) mem a Ha)|].
  split.
  { intros i Hi.
    assert (ZS : forall x, rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC -> aview segs (w_H W) mem x = Some 0).
    { intros x Hx. assert (Hin : inG [(rg_s fr_RG, 4 * ASRC)] x) by (apply inG_cons; left; exact Hx).
      pose proof (rng_all_in (fun a => fr_img a =? 0) [(rg_s fr_RG, 4 * ASRC)] x ltac:(vm_compute; reflexivity) Hin)
        as Hz.
      apply Z.eqb_eq in Hz. rewrite <- Hz. apply VIEW.
      apply (rng_cover (rg_s fr_RG) (4 * ASRC) G_fr_obj ltac:(vm_compute; reflexivity)). exact Hx. }
    split.
    - intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia].
      apply val_mem_of_view. intros k Hk. rewrite le_byte_0. apply ZS.
      clear -Hi Hj Hk. unfold ASRC in *. lia.
    - intros j Hj. assert (Hr : 0 <= ASRC * Z.of_nat i + j < 4 * ASRC) by (clear -Hi Hj; unfold ASRC in *; lia).
      pose proof (WR (rg_s fr_RG) (4 * ASRC) ltac:(vm_compute; reflexivity) _ Hr) as Hw.
      rewrite Z.add_assoc in Hw. exact Hw. }
  split.
  { exists 0. left. split; [reflexivity|]. split; [reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. split; [apply WR; vm_compute; reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. split; [apply WR; vm_compute; reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. apply WR; vm_compute; reflexivity. }
  split.
  { (* errno: its bytes are image bytes (seg_rom reads them), so they read in every memory, at some value *)
    assert (EB : forall k, (k < 4)%nat ->
      exists v, aview segs (w_H W) mem (as_errno B + Z.of_nat k) = Some v /\ 0 <= v < 256).
    { intros k Hk.
      assert (Hs : seg_rom segs (Z_to_bv 64 (as_errno B + Z.of_nat k)) <> None).
      { rewrite HEV. intros Hc. destruct k as [|[|[|[|k]]]]; [| | | | lia]; vm_compute in Hc; discriminate Hc. }
      destruct (aview segs (w_H W) mem (as_errno B + Z.of_nat k)) as [v|] eqn:E.
      - exists v. split; [reflexivity|]. destruct (aview_byte _ _ _ _ _ E) as (b & _ & Hb & Hr). exact Hr.
      - exfalso. apply Hs. revert E. unfold aview, mbyte.
        destruct (mrestrict (w_H W) mem (Z_to_bv 64 (as_errno B + Z.of_nat k))) as [b|];
          [intros Hc; cbn in Hc; discriminate Hc|].
        destruct (seg_rom segs (Z_to_bv 64 (as_errno B + Z.of_nat k))) as [b|];
          [intros Hc; cbn in Hc; discriminate Hc | intros _; reflexivity]. }
    destruct (EB 0%nat ltac:(lia)) as (v0 & E0 & R0). destruct (EB 1%nat ltac:(lia)) as (v1 & E1 & R1).
    destruct (EB 2%nat ltac:(lia)) as (v2 & E2 & R2). destruct (EB 3%nat ltac:(lia)) as (v3 & E3 & R3).
    exists (CTL (-1) 0 0 0 (v0 + 256 * (v1 + 256 * (v2 + 256 * v3)))), [], 0, 0, 0.
    split; [apply CELL; vm_compute; reflexivity|]. split; [apply WR; vm_compute; reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. split; [apply WR; vm_compute; reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. split; [apply WR; vm_compute; reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. split; [apply WR; vm_compute; reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. split; [apply WR; vm_compute; reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. split; [apply WR; vm_compute; reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. split; [apply WR; vm_compute; reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. split; [apply WR; vm_compute; reflexivity|].
    split.
    { apply val_mem_of_view. intros k Hk. pose proof (le_byte4 _ _ _ _ R0 R1 R2 R3 k Hk) as L4.
      destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth] in L4;
        (etransitivity; [first [exact E0 | exact E1 | exact E2 | exact E3] | f_equal; symmetry; exact L4]). }
    split; [intros i Hi; apply (c_glob_wr B HEV); apply (err_c B); lia|].
    cbv [ct_cl ct_br ct_dd ct_ei ct_ev].
    split; [exact (le_bytes4_range _ _ _ _ R0 R1 R2 R3)|].
    split; [right; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|].
    split; [left; reflexivity|]. split; [lia|]. split; [reflexivity|].
    left. split; [reflexivity|]. split; reflexivity. }
  split; [exists 0; split; [apply CELL; vm_compute; reflexivity|]; split; [apply WR; vm_compute; reflexivity | left; reflexivity]|].
  split.
  { split; [apply CELL; vm_compute; reflexivity|]. split; [apply CELL; vm_compute; reflexivity|].
    split; [apply CELL; vm_compute; reflexivity|]. apply WR; vm_compute; reflexivity. }
  split; [apply CELL; vm_compute; reflexivity|].
  split; [apply CELL; vm_compute; reflexivity|].
  split; [exists (2 ^ 32 - 1); apply CELL; vm_compute; reflexivity|].
  intros i Hi. apply (WR AG_LISTEN 4); [vm_compute; reflexivity | exact Hi].
Qed.

(* ------------------------------------------------------------------ why fr_blk_ok *)
(* AD1w_cf.v's fr_lib_inv_stable as it was at 3e82d89e10a, without fr_blk_ok: false at the real instance. *)
Definition fr_lib_inv_stable_v0 : Prop :=
  forall ci0 regs ly S (W : world segs) mem ly' S' (W' : world segs) mem',
  fr_LI B ci0 ly S W mem ->
  (forall a, inG GF a \/ inFP (fr_FP regs ly S W mem) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a /\
     (apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
     (writable_at segs (rd W mem) a -> writable_at segs (rd W' mem') a)) ->
  (forall b, In b (ablocks B ly S) -> In b (ablocks B ly' S')) ->
  fr_LI B ci0 ly' S' W' mem'.

Example fr_lib_inv_stable_v0_false : as_errno B = TFIB_ERRNO_A -> ~ fr_lib_inv_stable_v0.
Proof.
  intros HEV HS.
  assert (AB : ablocks B cx_ly cx_S = [(0, ATABLE)]) by reflexivity.
  assert (PRE : fr_LI B 0 cx_ly cx_S cx_W cx_mem).
  { split; [lia|].
    split; [intros a _; apply cx_wr|].
    split.
    { intros i Hi. split; [|intros j Hj; apply cx_wr].
      destruct i as [|[|[|[|i]]]]; [| | | | lia]; apply cx_garr8; vm_compute; reflexivity. }
    split.
    { exists 0. right.
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [cbn; lia|].
      split; [rewrite AB; left; reflexivity|].
      split; [exists (repeat (Z_to_bv 8 0) (Z.to_nat ATABLE)); split; [reflexivity|]; split; [reflexivity|];
              apply cx_garr8; vm_compute; reflexivity|].
      split; [constructor|]. split; constructor. }
    split.
    { exists (CTL (-1) 0 0 0 0), [], 0, 0, 0.
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      split; [rewrite HEV; apply cx_vm; vm_compute; reflexivity|]. split; [intros j Hj; apply cx_wr|].
      cbv [ct_cl ct_br ct_dd ct_ei ct_ev].
      split; [lia|]. split; [right; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|].
      split; [left; reflexivity|]. split; [lia|]. split; [reflexivity|].
      left. split; [reflexivity|]. split; reflexivity. }
    split; [exists 0; split; [apply cx_vm; vm_compute; reflexivity|];
      split; [intros j Hj; apply cx_wr | left; reflexivity]|].
    split.
    { split; [apply cx_vm; vm_compute; reflexivity|]. split; [apply cx_vm; vm_compute; reflexivity|].
      split; [apply cx_vm; vm_compute; reflexivity|]. intros j Hj; apply cx_wr. }
    split; [apply cx_vm; vm_compute; reflexivity|].
    split; [apply cx_vm; vm_compute; reflexivity|].
    split; [exists 0; apply cx_vm; vm_compute; reflexivity|].
    intros i Hi; apply cx_wr. }
  assert (FP0 : fr_FP (TEmpty : bvmap 5 word) cx_ly cx_S cx_W cx_mem = []) by (vm_compute; reflexivity).
  assert (KEEP : forall a, inG GF a \/ inFP (fr_FP (TEmpty : bvmap 5 word) cx_ly cx_S cx_W cx_mem) a ->
     aview segs (w_H cx_W) cx_mem' a = aview segs (w_H cx_W) cx_mem a /\
     (apresent (w_H cx_W) cx_mem a -> apresent (w_H cx_W) cx_mem' a) /\
     (writable_at segs (rd cx_W cx_mem) a -> writable_at segs (rd cx_W cx_mem') a)).
  { intros a [Ha | Ha]; [| rewrite FP0 in Ha; destruct (inFP_nil a Ha)].
    assert (Hr : 0 <= a < 2 ^ 64 /\ a <> 5).
    { rewrite (G_fr_c_val B HEV) in Ha.
      pose proof (rng_all_in (fun x => (6 <=? x) && (x <? 2 ^ 64)) (G_fr_obj ++ [(TFIB_ERRNO_A, 4)]) a
        ltac:(vm_compute; reflexivity) Ha) as Hb.
      apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
    assert (E : cx_mem' (Z_to_bv 64 a) = cx_mem (Z_to_bv 64 a)).
    { unfold cx_mem'. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. rewrite (proj2 (Z.eqb_neq a 5) (proj2 Hr)). reflexivity. }
    unfold aview, apresent, writable_at, wview, mbyte, mrestrict, cx_W. cbn [w_H]. rewrite E.
    split; [reflexivity|]. split; intros H; exact H. }
  pose proof (HS 0 (TEmpty : bvmap 5 word) cx_ly cx_S cx_W cx_mem cx_ly cx_S cx_W cx_mem' PRE KEEP (fun b Hb => Hb))
    as POST.
  destruct POST as (_ & _ & _ & (T & [(_ & _ & E) | A]) & _).
  - destruct E as (_ & _ & _ & _ & E5 & _).
    pose proof (E5 0%nat ltac:(lia)) as Hk. vm_compute in Hk. discriminate Hk.
  - destruct A as (_ & _ & _ & _ & _ & _ & _ & A8 & (tail & T1 & T2 & T3) & _).
    rewrite AB in A8. destruct A8 as [E8|[]]. injection E8 as ET. subst T.
    assert (H5 : (5 < length (bzs (concat (map entry_bytes []) ++ tail)))%nat).
    { unfold bzs. rewrite length_map. clear -T2. cbn [concat map app] in T2 |- *. unfold ATABLE in T2. lia. }
    destruct (T3 5%nat H5) as (V & _). pose proof (V 0%nat ltac:(lia)) as Hk. vm_compute in Hk. discriminate Hk.
Qed.
End inv.

Print Assumptions fr_lib_inv_stable_ok.
Print Assumptions fr_lib_inv_init_ok.
Print Assumptions fr_lib_inv_stable_v0_false.
