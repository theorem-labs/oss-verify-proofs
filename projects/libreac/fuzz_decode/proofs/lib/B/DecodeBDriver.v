(* fuzz_decode image B, composition step 5b row D-B-driver: the closing side's H_DRIVER (lib/B/DecodeBClose.v:180)
   from the relocated core's driver.  Rule 24: no function is proved here; this file composes proved core lemmas.
   It is image A's lib/A/DecodeADriver.v (a working branch e78f73ea695) at image B's names.

   H_DRIVER asks, at a hand-off state c of the start-up certificate (HS_ok), that c realizes SPECX, given the runtime
   walks and the FROZEN library slot PL.dec_lib_contract_x_all (lib/B/Prog/LLVMFuzzerTestOneInput_cg.v:156).  The
   core proves exactly that from its own slot: lib/B/YD1p.v:86 tfib_drv_main (drv_mainX_stmt, lib/B/YD1q.v:28) at the
   exists-fx' slot's float invariant (as YD1q.v tfib_srealizesXF instantiates it), with lib/B/YB1n.v:74 HS_ok_open and
   Reusable/YO01.v:159 specx_closedx_eq (the two steps of YD1q.v:54-61).

   The one difference between the two slots: the frozen pre dec_lib_pre_x has the conjunct rom_view segs W mem
   (Prog/LLVMFuzzerTestOneInput_cg.v:116) after arodata_okS; the core's tfib_lib_pre_xf (lib/B/YCfn.v:88) has not.
   rom_view is a fact of the state, not of a walk: for an in-rom byte a,
   - a not owned and not errno: arodata_okS, a conjunct of the core's pre (lib/B/YE01.v:191, its first disjunct is
     in_rom word for word);
   - a owned: AR's am_const at the record fact ro_owned_pinned B (lib/A/DecodeROPinned.v:48, a working branch
     2f6c3143ebd), through ro_img_word_byte / rom_owned_of_AR below, fuzz_boxreg's lib/A/Rt/StrncmpView.v
     lemmas over DecodeROPinned's definitions;
   - a errno: impossible, by dec_rom_no_errno B (lib/B/Prog/check_round_trip_cg.v:151, DecodeBClose.v HB_ROM_NO_ERRNO).

   Image B's core states its slot over lib/B/YCbq.v and lib/B/YE01.v, the frozen slot over lib/Reusable/YCbq.v.  The
   two YCbq files differ only in their header, the YImgTop Require and off_img, which afn_pre and ajournal precede, so
   the two afn_pre and the two ajournal are convertible.  The frozen slot's ameta_inv / arodata_okS are bound to
   lib/B/YE01.v's, the core's own.

   The meter: DecodeBClose.v, the frozen slot and image B's core all take lib/Reusable/YC5d.v's Record ameter_ops
   (-coreB eed1e8e317a deleted the core's copy lib/B/YC5d.v), so MT passes through unchanged.

   The Section's premises are what stays open, each named: HA_TFIBSYMS (TfibSyms B), HB_ROM_NO_ERRNO,
   HB_RO_OWNED_PINNED (at TfibB: lib/B/DecodeBROPinned.v:129 dec_ro_owned_pinned, a Theorem Labs lane 32078366d8d),
   MT_FREE (true at ameter_triv), RO_IN (the frozen slot's RLO..RHI inside in_ro_tfa).  dec_H_DRIVER_B is H_DRIVER at
   the core's concrete sink / meta / rodata predicates (YE00 / lib/B/YE01 at lib/B/YE2k.v tfib_K), its RA_LLVMF /
   A_EMPTY (lib/B/YCfn.v:22-23) and HS_ok := lib/B/YB1n.v:45 HS_ok; it drops H_DRIVER's two premises the driver does
   not use (universe_ok (as_universe B), arm_at_main rc): the core builds ARm at main itself (lib/B/YD1p.v:102
   tfib_AR <- lib/B/YD1f.v:244 <- lib/B/YD1g.v:1442 tfib_ARm <- Reusable/YG0r.v:275 ARm_init_intro). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_decode.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB12 YB1h YB01 YB1n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG0f YG00 YG01 YG0n YG0d YG0q YK04 YA0i YA0n YI16.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YE00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YE01 YCfn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeShape.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v YF0m YCeg YD1v YD1w YD1x YD1i YE2k.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YD1k YD1l YD1o YD1j YD2m.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YD1p YD1q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LLVMFuzzerTestOneInput_cg check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeROPinned.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require YD2l DecodeBROPinned.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YC5d.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance decode_shape.

Module PL := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LLVMFuzzerTestOneInput_cg.
Module PC := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_round_trip_cg.
Module RC5 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YC5d.
Module BC5 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YC5d.

(* ---- rom_view from a state's facts (fuzz_boxreg lib/A/Rt/StrncmpView.v, as lib/A/DecodeADriver.v ports it) ----
   ro_img_word / ro_owned_pinned are lib/A/DecodeROPinned.v's (image-generic: segs, B are parameters); the two lemmas
   over them are StrncmpView.v's. *)
Section rv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Local Notation ro_img_word := (DecodeROPinned.ro_img_word segs).
Local Notation ro_owned_pinned := (DecodeROPinned.ro_owned_pinned segs B).
(* Byte k of an image word is the image byte at a + k (StrncmpView.v ro_img_word_byte). *)
Lemma ro_img_word_byte : forall w a v, ro_img_word a w = Some v ->
0 <= v < 2 ^ (8 * Z.of_nat w) /\
forall k, (k < w)%nat ->
option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 (a + Z.of_nat k))) = Some (le_byte v w k).
Proof.
induction w as [|w IH]; intros a v H.
- cbn in H. injection H as <-. split; [cbn; lia | intros k Hk; lia].
- cbn [DecodeROPinned.ro_img_word] in H.
  destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:Eb; [|discriminate].
  destruct (ro_img_word (a + 1) w) as [v'|] eqn:Ev; [|discriminate].
  injection H as <-. destruct (IH (a + 1) v' Ev) as [Rv' Hv'].
  pose proof (u8_range b) as Rb.
  assert (P8 : 2 ^ (8 * Z.of_nat (S w)) = 256 * 2 ^ (8 * Z.of_nat w)).
  { rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. change (2 ^ 8) with 256. lia. }
  assert (Rv : 0 <= bv_unsigned b + 256 * v' < 2 ^ (8 * Z.of_nat (S w))) by (rewrite P8; lia).
  split; [exact Rv|].
  intros k Hk. unfold le_byte. rewrite (Z.mod_small _ _ Rv).
  destruct k as [|k].
  + cbn [Z.of_nat]. rewrite Z.add_0_r, Z.mul_0_r, Z.shiftr_0_r, Eb. cbn [option_map]. f_equal.
    rewrite (Z.mul_comm 256 v'), Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
  + assert (Hk' : (k < w)%nat) by lia. specialize (Hv' k Hk').
    replace (a + Z.of_nat (S k)) with (a + 1 + Z.of_nat k) by lia. rewrite Hv'. f_equal.
    unfold le_byte. rewrite (Z.mod_small v') by lia.
    rewrite !Z.shiftr_div_pow2 by lia.
    replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite <- Z.div_div by first [apply Z.pow_nonzero; lia | apply Z.pow_pos_nonneg; lia].
    replace ((bv_unsigned b + 256 * v') / 2 ^ 8) with v'; [reflexivity|].
    change (2 ^ 8) with 256. apply Z.div_unique with (r := bv_unsigned b); [left; lia | lia].
Qed.
(* An owned in-rom byte shows the image byte in every AR state (StrncmpView.v fm_rom_viewO_of_AR). *)
Lemma rom_owned_of_AR : forall ly S (W : world segs) mem md a,
ro_owned_pinned -> AR segs B ly S W mem md -> in_rom segs a -> Exists (in_zr a) (as_owned_static B) ->
aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Proof.
intros ly S W mem md a HP HA Hr Ho.
destruct HA as [HM _]. apply am_const in HM.
pose proof (HP ly a Hr Ho) as HE.
apply Exists_exists in HE as (c & Hc & a' & v & Ha & Hv & Hrg & Hw).
pose proof (proj1 (Forall_forall _ _) HM c Hc) as Hh. unfold cell_holds in Hh. cbv zeta in Hh.
rewrite Hv, Ha in Hh. cbn [aeval] in Hh.
destruct (ro_img_word_byte _ _ _ Hw) as [_ Hb].
assert (Hk : (Z.to_nat (a - a') < c_w c)%nat) by lia.
specialize (Hh _ Hk). specialize (Hb _ Hk).
replace (a' + Z.of_nat (Z.to_nat (a - a'))) with a in Hh, Hb by lia.
rewrite Hh, Hb. reflexivity.
Qed.
End rv.

Lemma in_zr_dec : forall a r, {in_zr a r} + {~ in_zr a r}.
Proof.
intros a [lo n]. unfold in_zr. cbn [fst snd].
destruct (Z_le_gt_dec lo a) as [H1|H1]; [|right; lia].
destruct (Z_lt_ge_dec a (lo + n)) as [H2|H2]; [left; lia | right; lia].
Qed.

Section a.
Variable B : asyms.
Hypothesis HA_TFIBSYMS : TfibSyms B.
Hypothesis HB_ROM_NO_ERRNO : PC.dec_rom_no_errno B.
Hypothesis HB_RO_OWNED_PINNED : DecodeROPinned.ro_owned_pinned tfibsegs B.
Variable MT : RC5.ameter_ops.
Hypothesis MT_FREE : forall S m, RC5.mo_ok MT S m.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.

Section RC. Context {rc : YM05.RunCeil}.

(* rom_view at any AR state whose view keeps the read-only bytes that are no owned static and no errno. *)
Lemma dec_rom_view_of_pre_B : forall ly S (W : world tfibsegs) mem md,
AR tfibsegs B ly S W mem md -> arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H W) mem) ->
rom_view tfibsegs W mem.
Proof.
intros ly S W mem md HAR HARO a Ha.
destruct (Exists_dec (in_zr a) (as_owned_static B) (in_zr_dec a)) as [Ho|Ho].
- exact (rom_owned_of_AR tfibsegs B ly S W mem md a HB_RO_OWNED_PINNED HAR Ha Ho).
- apply HARO; [left; exact Ha | exact Ho | exact (HB_ROM_NO_ERRNO a Ha)].
Qed.

(* The frozen slot gives the core's exists-fx' slot. *)
Lemma dec_contract_xf_of_x_B : forall fx : YK11.FPState,
@PL.dec_lib_contract_x fx rc decode_shape asink_syms tfib_K asink_none ameta_inv arodata_okS YCfn.RA_LLVMF YCfn.A_EMPTY
  B MT XL XL RLO RHI ->
@tfib_lib_contract_xf fx rc decode_shape B MT XL XL RLO RHI.
Proof.
intros fx DEC ly S W regs mem md p n pl M K HAI HPRE CONT.
destruct HPRE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
pose proof (dec_rom_view_of_pre_B ly S W mem md (proj1 H1) H11) as HROM.
exact (DEC ly S W regs mem md p n pl M K HAI
  (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj HROM
  (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 H17)))))))))))))))))
  CONT).
Qed.

(* H_DRIVER (DecodeBClose.v:180) at the core's instances, from the core's driver. *)
Theorem dec_H_DRIVER_B :
  (forall fx : YK11.FPState, @amalloc_realizes fx rc decodesegsB0 B) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc decodesegsB0 B) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc decodesegsB0 B OCpy (pc_wrap_memcpy (as_code B))) ->
  @PL.dec_lib_contract_x_all rc decode_shape asink_syms tfib_K asink_none ameta_inv arodata_okS
    YCfn.RA_LLVMF YCfn.A_EMPTY B MT XL XL RLO RHI ->
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (c : config),
  valid_sp sp -> valid_brk decodesegsB0 brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  HS_ok h sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (in_fs inp) c ->
  srealizes decodesegsB0 c (SPECX (LS:=decode_shape) inp).
Proof.
intros AM AF AI LIB sp rdraw brk inp h c Hsp Hbrk Hfit Hinp Hceil Hok.
destruct (HS_ok_open h sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (in_fs inp) c Hok)
  as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
apply (srz_conseq tfibsegs _ (CLOSEDX inp)); [| apply t_eq_sym; apply specx_closedx_eq].
set (P := fun fx : YK11.FPState => frm_zero (@fp_csr fx)).
assert (LIBC : forall fx : YK11.FPState, P fx -> tfib_lib_contract_xP (fx := fx) B MT XL XL RLO RHI P).
{ intros fx Hz.
  exact (tfib_lib_contract_xP_of_xf (fx := fx) B MT XL XL RLO RHI Hz (dec_contract_xf_of_x_B fx (LIB fx))). }
exact (tfib_drv_main P fp_frm_zero_fx0 B HA_TFIBSYMS (AM YK11.fx0) (fun fx _ => AF fx) (AI YK11.fx0)
  (tfib_ARDCHK B HA_TFIBSYMS) MT XL XL RLO RHI MT_FREE RO_IN LIBC
  YD1k.xst tfib_xst_frame
  (fun fx _ => tfib_printf_first (fx := fx) B HA_TFIBSYMS (AR_laws_ok tfibsegs B) HA_TFIBSYMS)
  (fun fx _ => tfib_printf_next (fx := fx) B HA_TFIBSYMS (AR_laws_ok tfibsegs B) HA_TFIBSYMS)
  YD1k.est tfib_est_img tfib_est_frame
  (tfib_fwrite_site B HA_TFIBSYMS (AR_laws_ok tfibsegs B))
  (tfib_refused_site B HA_TFIBSYMS (AR_laws_ok tfibsegs B) HA_TFIBSYMS)
  (tfib_fprintf_open_site B HA_TFIBSYMS (AR_laws_ok tfibsegs B) HA_TFIBSYMS)
  (tfib_fprintf_rderr_site B HA_TFIBSYMS (AR_laws_ok tfibsegs B) HA_TFIBSYMS)
  (tfib_fprintf_usage_site B HA_TFIBSYMS (AR_laws_ok tfibsegs B) HA_TFIBSYMS)
  (fun fx _ => tfib_exit_site (fx := fx) B HA_TFIBSYMS (AR_laws_ok tfibsegs B))
  sp rdraw brk inp h ch E R FULL model Hsp Hbrk Hfit Hinp Hceil Hch HC HE HM).
Qed.
End RC.
End a.

(* At decode B's record TfibB (lib/B/YD2l.v:12): TfibSyms is YD2l.v:68 TfibB_syms and ro_owned_pinned is
   lib/B/DecodeBROPinned.v:129 dec_ro_owned_pinned (a Theorem Labs lane, a vm_compute gate over the generated record). *)
Theorem dec_H_DRIVER_TfibB : forall (MT : RC5.ameter_ops) (XL : Z -> Z) (RLO RHI : Z) {rc : YM05.RunCeil},
  PC.dec_rom_no_errno YD2l.TfibB ->
  (forall S m, RC5.mo_ok MT S m) ->
  (forall a, RLO <= a < RHI -> in_ro_tfa a) ->
  (forall fx : YK11.FPState, @amalloc_realizes fx rc decodesegsB0 YD2l.TfibB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc decodesegsB0 YD2l.TfibB) ->
  (forall fx : YK11.FPState,
     @aintrin_realizes fx rc decodesegsB0 YD2l.TfibB OCpy (pc_wrap_memcpy (as_code YD2l.TfibB))) ->
  @PL.dec_lib_contract_x_all rc decode_shape asink_syms tfib_K asink_none ameta_inv arodata_okS
    YCfn.RA_LLVMF YCfn.A_EMPTY YD2l.TfibB MT XL XL RLO RHI ->
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (c : config),
  valid_sp sp -> valid_brk decodesegsB0 brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  HS_ok h sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (in_fs inp) c ->
  srealizes decodesegsB0 c (SPECX (LS:=decode_shape) inp).
Proof.
intros MT XL RLO RHI rc HNOE MTF ROI.
exact (@dec_H_DRIVER_B YD2l.TfibB YD2l.TfibB_syms HNOE DecodeBROPinned.dec_ro_owned_pinned MT MTF XL RLO RHI ROI rc).
Qed.

Print Assumptions dec_H_DRIVER_TfibB.
