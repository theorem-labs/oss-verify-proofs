(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfPcW.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* musl printf_core (fm.asan 0x8f278), second pass: the walk invariant and the steps the per-format walks are made of
   (engine runs, the __fwritex / strnlen calls through their contracts, the NUL read, a branch, the return). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfPc0 FMsnprintfPcA FMsnprintfPcV.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Set Default Proof Using "All".
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis AFWX : afwx_realizesU B A_FWX.
Hypothesis ASNL : astrnlen_realizesU B W_STRNLEN.
Hypothesis ASNLN : astrnlenN_realizesU B W_STRNLEN.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (sp0 D N M P : Z) (nsl : nat).
Hypothesis HB : snk_base B ly S U W mem0 md0 sp0.
Hypothesis HD : snk_dest B ly S W mem0 D M.
Hypothesis HMN : M <= N.
Hypothesis HRV : rom_viewN tfibsegs B W mem0.
Hypothesis HR : snk_regs B regs0 (sp0 + OSP_PC).
Hypothesis HP1 : sp0 + 0x200 <= P.
Hypothesis HP2 : P + 8 * Z.of_nat nsl <= ly_stk_hi ly.
(* the walk invariant: the frame apcore promises so far, and the sink holding the bytes out *)
Definition PI (out : list Z) (mem : word -> option byte) (md : Model) : Prop :=
  snk_frame B ly S U W mem0 md0 sp0 (sp0 + OSP_PC + 8) (fw_xw sp0 D M) mem md /\ (exists b, SNK W mem sp0 D N out b) /\
  Z.of_nat (length out) + 1 <= M.
Definition EF (E : env) : Prop :=
  bv_unsigned (ew E 2) = sp0 /\ bv_unsigned (ew E 32) = P /\
  (forall i (r : bv 5), (i < 32)%nat -> i <> 2%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr regs0 r).
(* the walk state: the symbolic state, the invariant, the frame base and the entry registers, the atoms A pinned *)
Definition WS (A : list (nat * Z)) (out : list Z) (E : env) (ss : sstate) (ms : machine_state) (md : Model) : Prop :=
  st_ok tfibsegs E ss (restrict (w_H W) ms) /\ ss_resv ss = None /\ PI out (ms_mem ms) md /\ EF E /\
  Forall (fun p => bv_unsigned (ew E (fst p)) = snd p) A.

Lemma hb_facts : alloc_ceiling <= ly_stk_lo ly /\ 2 ^ 44 <= sp0 /\ sp0 mod 16 = 0 /\ ly_stk_lo ly + SNK_STK <= sp0 /\
  sp0 + 0x200 <= ly_stk_hi ly /\ sp0 + 0x200 <= 2 ^ 47 /\ kHighMemBeg <= sp0 - SNK_STK /\ ly_stk_hi ly <= 2 ^ 47.
Proof.
destruct HB as (HA & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
pose proof (am_layout B ly S _ (ARU_ARm tfibsegs B ly S U W mem0 md0 HA)) as HLY.
pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _). unfold kHighMemEnd in Lhi.
repeat split; assumption.
Qed.
Lemma hd_facts : 0 < D /\ D + M <= alloc_ceiling /\ 1 <= M <= 2 ^ 30 /\ (D + M <= FM_canary \/ FM_canary + 8 <= D) /\
  amem_range D M.
Proof. destruct HD as (H1 & H2 & H3 & H4 & _ & H6 & _). repeat split; try assumption; lia. Qed.
Ltac geo := pose proof hb_facts as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G7'); pose proof hd_facts as (G8 & G9 & G10 & G11 & G12);
  pose proof alloc_ceiling_val as G13; unfold amem_range in *; unfold SNK_STK, OSP_PC, OSP_FW, IBO, CKO, FO, kHighMemBeg,
  kLowMemEnd, kHighMemEnd, FM_canary, SHADOW_OFF in *.
(* bytes below the band (or above it) and off the destination are kept by the frame *)
Lemma pi_view : forall out mem md a, PI out mem md -> 0 <= a < 2 ^ 64 -> (a < sp0 - SNK_STK \/ sp0 + 0x200 <= a) ->
  ~ (D <= a < D + M) -> aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a.
Proof.
intros out mem md a ((_ & _ & _ & Hfr & _) & _) Ha Hb Hd. apply Hfr; [exact Ha | geo; lia |].
unfold fw_xw. geo. lia.
Qed.
Lemma pi_pres : forall out mem md a, PI out mem md -> apresent (w_H W) mem0 a -> apresent (w_H W) mem a.
Proof. intros out mem md a ((_ & _ & _ & _ & Hp) & _) H. exact (Hp a H). Qed.
Lemma pi_vis : forall out mem md a, PI out mem md -> aview tfibsegs (w_H W) mem0 a <> None -> aview tfibsegs (w_H W) mem a <> None.
Proof. intros out mem md a ((_ & _ & _ & _ & Hp) & _) H. exact (aview_some_mono _ _ _ a Hp H). Qed.
(* shadow bytes of application memory are neither in the band nor in the destination *)
Lemma shadow_out : forall x, 0 <= x < 2 ^ 47 ->
  SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < kHighMemBeg /\ ~ (D <= shadow_of_addr SHADOW_OFF x < D + M).
Proof. intros x Hx. unfold shadow_of_addr. geo. split; [split|]; [ | | ]; Z.div_mod_to_equations; lia. Qed.
Lemma pi_shadow : forall out mem md s, PI out mem md -> SHADOW_OFF <= s < kHighMemBeg -> ~ (D <= s < D + M) ->
  aview tfibsegs (w_H W) mem s = aview tfibsegs (w_H W) mem0 s.
Proof. intros out mem md s H Hs Hd. apply (pi_view out mem md s H); [geo; lia | geo; lia | exact Hd]. Qed.
Lemma pi_ra : forall out mem md x n, PI out mem md -> 0 <= x -> x + n <= 2 ^ 47 ->
  range_addressable (aview tfibsegs (w_H W) mem0) SHADOW_OFF x n -> range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros out mem md x n H Hx Hn Hra y Hy. destruct (Hra y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
destruct (shadow_out y ltac:(lia)) as (Hs1 & Hs2). rewrite (pi_shadow out mem md _ H Hs1 Hs2). exact Hs.
Qed.
Lemma pi_hull : forall out mem md x n, PI out mem md -> 0 <= x -> x + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem0) x n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Proof.
intros out mem md x n H Hx Hn Hn0 Hh s Hs. pose proof (Hh s Hs) as Hv. apply (pi_vis out mem md s H Hv).
Qed.
Lemma pi_zshadow : forall out mem md, PI out mem md ->
  zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (sp0 - SNK_STK) (SNK_STK + 0x200).
Proof.
intros out mem md H i Hi. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hz).
pose proof (Hz i Hi) as Hzi. assert (Hii : 0 <= i < 1202) by (unfold SNK_STK in Hi; cbn in Hi; lia).
destruct (shadow_out (sp0 - SNK_STK) ltac:(geo; lia)) as (Hs1 & Hs2).
unfold shadow_of_addr in *. rewrite (pi_shadow out mem md _ H); [exact Hzi | geo; Z.div_mod_to_equations; lia | geo; Z.div_mod_to_equations; lia].
Qed.
Lemma val_mem_xfer : forall (mem mem' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> aview tfibsegs (w_H W) mem' (a + Z.of_nat k) = aview tfibsegs (w_H W) mem (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a n v -> val_mem tfibsegs (mrestrict (w_H W) mem') a n v.
Proof. intros mem mem' a n v He Hv k Hk. rewrite (mbyte_of_aview _ _ _ _ _ (He k Hk)). exact (Hv k Hk). Qed.
Definition snk_cell (a : Z) : Prop :=
  (sp0 + IBO <= a < sp0 + IBO + 80) \/ (sp0 + FO <= a < sp0 + FO + 160) \/ (sp0 + CKO <= a < sp0 + CKO + 16) \/ (D <= a < D + M).
Lemma SNK_xfer : forall mem mem' out b, SNK W mem sp0 D N out b -> Z.of_nat (length out) + 1 <= M ->
  (forall a, snk_cell a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) -> SNK W mem' sp0 D N out b.
Proof.
intros mem mem' out b (S0 & S32 & S40 & S56 & S72 & S88 & S144 & S152 & SC0 & SC8 & SIB & SD & SDn & [Hb1 Hb2] & Hbo & Ho & HN & Hf) HoM He.
unfold snk_cell, IBO, CKO, FO in He.
repeat split; try assumption;
  try (eapply val_mem_xfer; [|eassumption]; intros k Hk; apply He; unfold CKO, FO; cbn in Hk; lia).
- intros i Hi. rewrite He by (unfold IBO in *; lia). exact (SIB i Hi).
- intros i Hi. rewrite He by lia. exact (SD i Hi).
- rewrite He by lia. exact SDn.
Qed.
(* ---- engine runs: the symbolic state writes only the stack window [sp0 - SNK_STK, sp0 + OSP_PC + 8) ---- *)
Definition winok (ws : list (option nat * Z * Z)) : bool :=
  match ws with
  | (Some 2%nat, lo, hi) :: rest => (lo =? - SNK_STK) && (hi =? OSP_PC + 8) && forallb (fun t => snd t <=? snd (fst t)) rest
  | _ => false
  end.
Lemma winok_in : forall E rs a, winok (windows rs) = true -> bv_unsigned (ew E 2) = sp0 -> in_wrange E rs a ->
  sp0 - SNK_STK <= a < sp0 + OSP_PC + 8.
Proof.
intros E rs a Hw Hsp Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr).
unfold winok in Hw. destruct (windows rs) as [|[[[[|[|[|n]]]|] lo0] hi0] rest]; try discriminate Hw.
apply andb_prop in Hw as [Hw Hr0]. apply andb_prop in Hw as [Hl Hh]. apply Z.eqb_eq in Hl. apply Z.eqb_eq in Hh.
destruct Ht as [Ht|Ht].
- injection Ht as <- <- <-. cbn [base_val] in Hr. lia.
- rewrite forallb_forall in Hr0. specialize (Hr0 _ Ht). cbn [fst snd] in Hr0. apply Z.leb_le in Hr0. lia.
Qed.
Lemma winok_hd : forall E rs a, winok (windows rs) = true -> bv_unsigned (ew E 2) = sp0 ->
  sp0 - SNK_STK <= a < sp0 + OSP_PC + 8 -> in_wrange E rs a.
Proof.
intros E rs a Hw Hsp Ha. unfold winok, windows in Hw. destruct rs as [|r rest]; [discriminate Hw|].
cbn [map] in Hw. destruct (YP09.r_base r) as [[|[|[|n]]]|] eqn:Eb; try discriminate Hw.
apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hl Hh]. apply Z.eqb_eq in Hl. apply Z.eqb_eq in Hh.
exists r. split; [left; reflexivity|]. rewrite Eb. cbn [base_val]. lia.
Qed.
Lemma win_writable' : forall E ss ms a, st_ok tfibsegs E ss ms -> in_wrange E (ss_mem ss) a -> writable_at tfibsegs (ms_mem ms) a.
Proof.
intros E ss ms a HS (r & Hin & Ha).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _).
pose proof (proj1 (Forall_forall _ _) Hok r Hin) as (_ & _ & Hw & _).
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.
Lemma PI_run : forall out mem md memB mat, PI out mem md ->
  (forall z : word, ~ (sp0 - SNK_STK <= bv_unsigned z < sp0 + OSP_PC + 8) -> memB z = mem z) ->
  (forall a, snk_band sp0 a -> apresent (w_H W) memB a) ->
  PI out memB (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros out mem md memB mat ((HA & Hsb & Hp & Hfr & Hpm) & (b & HS) & HoM) HF HpB.
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < sp0 + OSP_PC + 8) ->
  aview tfibsegs (w_H W) memB a = aview tfibsegs (w_H W) mem a).
{ intros a Hr Ha. apply YF0x.aview_same. apply HF. rewrite unsigned_lit_small by lia. exact Ha. }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
split; [split; [|split; [|split; [exact HpB|split]]]|].
- apply (ARU_frame tfibsegs B LAWS ly S U W mem md memB _ HA).
  + intros a Hr Hown. apply AVB; [exact Hr|]. intros Hs.
    exact (ARU_stack tfibsegs B LAWS ly S U W mem md a HA ltac:(geo; lia) Hown).
  + intros a Hv. rewrite (YE2y.aview_mod (w_H W) memB a). rewrite (YE2y.aview_mod (w_H W) mem a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 - SNK_STK)) as [L1|L1]; [rewrite AVB by lia; exact Hv|].
    destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 + OSP_PC + 8)) as [L2|L2]; [| rewrite AVB by lia; exact Hv].
    apply YE2y.aview_some_of_apresent. apply HpB. unfold snk_band. geo. lia.
  + apply MF. + apply MF. + apply MF.
  + intros a Ha Hh. unfold YG0d.w64 in Hh |- *.
    assert (Har : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
    destruct (Z_lt_le_dec a (sp0 - SNK_STK)) as [L1|L1]; [apply HF; rewrite unsigned_lit_small by lia; lia|].
    destruct (Z_lt_le_dec a (sp0 + OSP_PC + 8)) as [L2|L2];
      [exfalso; destruct (HpB a ltac:(unfold snk_band; geo; lia)) as [Hf _]; rewrite Hf in Hh; discriminate Hh|].
    apply HF. rewrite unsigned_lit_small by lia. lia.
- eapply same_but_materialized_trans; [exact Hsb | apply with_vm_backing_same].
- intros a Hr Hb Hx. rewrite (AVB a Hr) by (geo; lia). exact (Hfr a Hr Hb Hx).
- intros a Hpa. pose proof (Hpm a Hpa) as Hpa'.
  rewrite (YE2y.apresent_mod _ memB a). rewrite (YE2y.apresent_mod _ mem a) in Hpa'.
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 - SNK_STK)) as [L1|L1];
    [apply (YF0x.apresent_same (w_H W) mem memB _); [apply HF; rewrite unsigned_lit_small by lia; lia | exact Hpa']|].
  destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 + OSP_PC + 8)) as [L2|L2];
    [apply HpB; unfold snk_band; geo; lia|].
  apply (YF0x.apresent_same (w_H W) mem memB _); [apply HF; rewrite unsigned_lit_small by lia; lia | exact Hpa'].
- split; [|exact HoM]. exists b. apply (SNK_xfer mem memB out b HS HoM). intros a Ha. unfold snk_cell in Ha.
  apply AVB; [geo; lia | geo; lia].
Qed.
Lemma step_run : forall A out E ss ss' st ms md Q,
  WS A out E ss ms md -> PRUN ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
  winok (windows (ss_mem ss)) = true -> winok (windows (ss_mem ss')) = true -> ss_resv ss' = None ->
  (forall ms' md', WS A out E ss' ms' md' -> SRr tfibsegs W (mkCfg ms' md') Q) -> SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros A out E ss ss' st ms md Q (HS & Hrv & HPI & HEF & HA) Hrun Hst Hw Hw' Hrv' HK.
eapply (SRr_run_to_gen tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx_tfa W FUEL A_FWX E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr.
assert (HS1' : st_ok tfibsegs E ss' (restrict (w_H W) ms1)) by (destruct st; [exact HS1 | contradiction | exact HS1]).
apply HK. split; [exact HS1'|]. split; [exact Hrv'|]. split; [|exact (conj HEF HA)].
destruct HEF as (H2 & _).
apply (PI_run out (ms_mem ms) md (ms_mem ms1) mat1 HPI).
- intros z Hz. apply HF. intros Hin. apply Hz. exact (winok_in E _ _ Hw H2 Hin).
- intros a Ha. destruct (Z_lt_le_dec a (sp0 + OSP_PC + 8)) as [L|L].
  + assert (Hin : in_wrange E (ss_mem ss') a) by (apply (winok_hd E _ a Hw' H2); unfold snk_band in Ha; lia).
    pose proof (win_writable' E ss' (restrict (w_H W) ms1) a HS1' Hin) as Hwr. cbn [restrict ms_mem] in Hwr.
    apply (YE7f.apresent_of_writable (w_H W) (ms_mem ms1) a); [unfold snk_band in Ha; geo; lia | apply YE7f.high_not_img; unfold snk_band in Ha; geo; lia | exact Hwr].
  + destruct HPI as ((_ & _ & Hp & _) & _). pose proof (Hp a Ha) as [Hh [bb Hbb]]. split; [exact Hh|]. exists bb.
    rewrite (HF (Z_to_bv 64 a)); [exact Hbb|]. rewrite unsigned_lit_small by (unfold snk_band in Ha; geo; lia).
    intros Hin. pose proof (winok_in E _ _ Hw H2 Hin). lia.
Qed.
(* ---- calls: the structural facts kcall asks, as one boolean the walks compute ---- *)
Fixpoint skel_eqb (x y : list (option nat * Z * Z * Z * Z)) : bool :=
  match x, y with
  | [], [] => true
  | (b1, l1, h1, wl1, wh1) :: x', (b2, l2, h2, wl2, wh2) :: y' =>
      obase_eqb b1 b2 && (l1 =? l2) && (h1 =? h2) && (wl1 =? wl2) && (wh1 =? wh2) && skel_eqb x' y'
  | _, _ => false
  end.
Lemma skel_eqb_eq : forall x y, skel_eqb x y = true -> x = y.
Proof.
induction x as [|[[[[b1 l1] h1] wl1] wh1] x IH]; intros [|[[[[b2 l2] h2] wl2] wh2] y] H; cbn in H; try discriminate; [reflexivity|].
repeat (apply andb_prop in H as [H ?]).
repeat match goal with Hz : (_ =? _) = true |- _ => apply Z.eqb_eq in Hz end.
assert (b1 = b2) by (destruct b1, b2; cbn in H; try discriminate; [apply Nat.eqb_eq in H; congruence | reflexivity]).
subst. f_equal. apply IH. assumption.
Qed.
Definition callchk (k : nat) (ra osp xlo xhi : Z) (ss : sstate) : bool :=
  match ss_mem ss with
  | r0 :: rest =>
      match YP09.r_base r0 with Some 2%nat => true | _ => false end &&
      (YP09.r_lo r0 =? - SNK_STK) && (YP09.r_hi r0 =? 0) && (- SNK_STK <=? YP09.r_wlo r0) && (YP09.r_whi r0 <=? 0) &&
      forallb (chunk_inside r0) (YP09.r_chunks r0) && skel_eqb (skeleton rest) (skeleton (pc_rest nsl)) &&
      sv_eqb (sr_get (ss_regs ss) 1%bv) (SLit ra) && sv_eqb (sr_get (ss_regs ss) 2%bv) (SOff 2 osp) &&
      sv_eqb (sr_get (ss_regs ss) 3%bv) (SOff 3 0) && sv_eqb (sr_get (ss_regs ss) 4%bv) (SOff 4 0) &&
      ss_atoms_lt k ss && regions_wf (ss_mem (kafter k ss ra osp xlo xhi)) &&
      no_cdata (ss_mem (kafter k ss ra osp xlo xhi)) && mem_atoms_lt k (ss_mem (kafter k ss ra osp xlo xhi)) &&
      (0 <=? ra) && (ra <? 2 ^ 64) && (ra mod 2 =? 0) && (33 <=? k)%nat
  | [] => false
  end.
Lemma callchk_sound : forall k ra osp xlo xhi ss, callchk k ra osp xlo xhi ss = true ->
  exists r0 rest, ss_mem ss = r0 :: rest /\ YP09.r_base r0 = Some 2%nat /\ YP09.r_lo r0 = - SNK_STK /\ YP09.r_hi r0 = 0 /\
  - SNK_STK <= YP09.r_wlo r0 /\ YP09.r_whi r0 <= 0 /\ forallb (chunk_inside r0) (YP09.r_chunks r0) = true /\
  skeleton rest = skeleton (pc_rest nsl) /\
  sr_get (ss_regs ss) 1%bv = SLit ra /\ sr_get (ss_regs ss) 2%bv = SOff 2 osp /\
  sr_get (ss_regs ss) 3%bv = SOff 3 0 /\ sr_get (ss_regs ss) 4%bv = SOff 4 0 /\
  ss_atoms_lt k ss = true /\ regions_wf (ss_mem (kafter k ss ra osp xlo xhi)) = true /\
  no_cdata (ss_mem (kafter k ss ra osp xlo xhi)) = true /\ mem_atoms_lt k (ss_mem (kafter k ss ra osp xlo xhi)) = true /\
  0 <= ra < 2 ^ 64 /\ ra mod 2 = 0 /\ (33 <= k)%nat.
Proof.
intros k ra osp xlo xhi ss H. unfold callchk in H. destruct (ss_mem ss) as [|r0 rest] eqn:Em; [discriminate H|].
repeat (apply andb_prop in H as [H ?]).
destruct (YP09.r_base r0) as [[|[|[|n]]]|] eqn:Eb; try discriminate H.
repeat match goal with
  | Hz : (_ =? _) = true |- _ => apply Z.eqb_eq in Hz
  | Hz : (_ <=? _) = true |- _ => apply Z.leb_le in Hz
  | Hz : (_ <? _) = true |- _ => apply Z.ltb_lt in Hz
  | Hz : (_ <=? _)%nat = true |- _ => apply Nat.leb_le in Hz
  | Hz : sv_eqb _ _ = true |- _ => apply sv_eqb_eq in Hz
  | Hz : skel_eqb _ _ = true |- _ => apply skel_eqb_eq in Hz
  end.
exists r0, rest. repeat split; try assumption; try reflexivity; lia.
Qed.
Lemma skel_rest : skeleton (pc_rest nsl) =
  [(Some 2%nat, FO, FO + 4, FO, FO); (None, FM_canary, FM_canary + 8, 0, 0); (Some 32%nat, 0, 8 * Z.of_nat nsl, 0, 0);
   (None, IMG_RO_LO, IMG_RO_HI, 0, 0)].
Proof. reflexivity. Qed.
Lemma rest_ext : forall E rest r a, skeleton rest = skeleton (pc_rest nsl) -> EF E -> In r rest ->
  base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
  (sp0 + FO <= a < sp0 + FO + 4) \/ (FM_canary <= a < FM_canary + 8) \/ (P <= a < P + 8 * Z.of_nat nsl) \/
  (IMG_RO_LO <= a < IMG_RO_HI).
Proof.
intros E rest r a Hsk (H2 & H32 & _) Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk, skel_rest in Hin.
destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn [YP09.r_base YP09.r_lo YP09.r_hi] in Ha.
destruct Hin as [Hq|[Hq|[Hq|[Hq|[]]]]]; injection Hq as Hq1 Hq2 Hq3 _ _; subst b lo hi; cbn [base_val] in Ha; rewrite ?H2, ?H32 in Ha; lia.
Qed.
Lemma rest_win : forall E rest r a, skeleton rest = skeleton (pc_rest nsl) -> In r rest ->
  base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> False.
Proof.
intros E rest r a Hsk Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk, skel_rest in Hin.
destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha.
destruct Hin as [Hq|[Hq|[Hq|[Hq|[]]]]]; injection Hq as Hq1 _ _ Hq4 Hq5; subst b wlo whi; lia.
Qed.
Lemma rest_away : forall a,
  (sp0 + FO <= a < sp0 + FO + 4) \/ (FM_canary <= a < FM_canary + 8) \/ (P <= a < P + 8 * Z.of_nat nsl) \/
  (IMG_RO_LO <= a < IMG_RO_HI) ->
  0 <= a < 2 ^ 64 /\ ~ (sp0 - SNK_STK <= a < sp0) /\ ~ fw_xw sp0 D M a.
Proof.
intros a Ha. destruct HD as (_ & _ & _ & _ & HDb & _).
assert (Hrom : IMG_RO_LO <= a < IMG_RO_HI -> ~ (D <= a < D + M)).
{ intros Hr Hd. destruct (HDb a Hd) as (_ & _ & Hno). apply Hno. apply in_rom_seg0. unfold IMG_RO_LO, IMG_RO_HI in Hr. lia. }
unfold fw_xw. unfold IMG_RO_LO, IMG_RO_HI in *. geo.
destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | lia | lia | specialize (Hrom Ha); lia].
Qed.
Lemma pi_base : forall out mem md, PI out mem md -> snk_base B ly S U W mem md sp0.
Proof.
intros out mem md H. pose proof H as ((HA & _ & Hp & _ & _) & _).
destruct HB as (_ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _ & _).
exact (conj HA (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj Hp (pi_zshadow out mem md H)))))))))).
Qed.
Lemma pi_dest : forall out mem md, PI out mem md -> snk_dest B ly S W mem D M.
Proof.
intros out mem md H. pose proof H as ((_ & _ & _ & _ & Hpm) & _).
destruct HD as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split.
- intros a Ha. destruct (H5 a Ha) as (Hw & Ho & Hr). split; [exact (writable_mono _ _ _ a Hpm Hw)|]. split; assumption.
- split; [exact H6|]. split; [apply (pi_ra out mem md D M H); [geo; lia | geo; lia | exact H7]|].
  apply (pi_hull out mem md D M H); [geo; lia | geo; lia | lia | exact H8].
Qed.
Lemma regsT_sp : forall E ss ms osp, st_ok tfibsegs E ss (restrict (w_H W) ms) -> bv_unsigned (ew E 2) = sp0 ->
  sr_get (ss_regs ss) 2%bv = SOff 2 osp -> getr (ms_regs ms) 2 = w64 (sp0 + osp).
Proof. intros E ss ms osp HS H2 S2. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite H2. reflexivity. Qed.
Lemma regsT_gt : forall E ss ms (r : bv 5) i, st_ok tfibsegs E ss (restrict (w_H W) ms) -> EF E ->
  (i < 32)%nat -> i <> 2%nat -> Z.of_nat i = bv_unsigned r -> sr_get (ss_regs ss) r = SOff i 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms r i HS (_ & _ & HE) Hi Hi2 Hr Sr. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ r HS), Sr. cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (HE i r Hi Hi2 Hr).
Qed.
Lemma EF_havoc : forall E k ws, EF E -> (33 <= k)%nat -> EF (havoc E k ws).
Proof.
intros E k ws (H2 & H32 & HE) Hk. split; [rewrite ew_havoc_old by lia; exact H2|]. split; [rewrite ew_havoc_old by lia; exact H32|].
intros i r Hi Hi2 Hr. rewrite ew_havoc_old by lia. exact (HE i r Hi Hi2 Hr).
Qed.
Lemma A_havoc : forall E k ws (A : list (nat * Z)), Forall (fun p => bv_unsigned (ew E (fst p)) = snd p) A ->
  forallb (fun p => (fst p <? k)%nat) A = true -> Forall (fun p => bv_unsigned (ew (havoc E k ws) (fst p)) = snd p) A.
Proof.
intros E k ws A HA Hk. rewrite Forall_forall in HA |- *. rewrite forallb_forall in Hk. intros p Hp.
pose proof (Hk p Hp) as Hl. apply Nat.ltb_lt in Hl. rewrite ew_havoc_old by exact Hl. exact (HA p Hp).
Qed.
Lemma kafter_resv : forall k ss ra osp xlo xhi, ss_mem ss <> [] -> ss_resv (kafter k ss ra osp xlo xhi) = None.
Proof. intros k ss ra osp xlo xhi H. unfold kafter. destruct (ss_mem ss); [contradiction | reflexivity]. Qed.
(* __fwritex (x, l, f) from out(): AFWX appends bs to the sink *)
Lemma step_fwx : forall A out E ss ms md k ra x bs Q,
  WS A out E ss ms md -> ss_pc ss = A_FWX -> callchk k ra OSP_FW IBO (IBO + 80) ss = true ->
  sv_denot E (sr_get (ss_regs ss) 10%bv) = w64 x -> sv_denot E (sr_get (ss_regs ss) 11%bv) = w64 (Z.of_nat (length bs)) ->
  sr_get (ss_regs ss) 12%bv = SOff 2 FO ->
  fw_src W (ms_mem ms) D M x bs -> Z.of_nat (length out) + Z.of_nat (length bs) + 1 <= M ->
  forallb (fun p => (fst p <? k)%nat) A = true ->
  (forall E' ms' md', WS A (out ++ bs) E' (kafter k ss ra OSP_FW IBO (IBO + 80)) ms' md' -> SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros A out E ss ms md k ra x bs Q (HS & Hrv & HPI & HEF & HA) Hpc Hck H10 H11 S12 Hsrc Hroom HAk HK.
destruct (callchk_sound _ _ _ _ _ _ Hck) as (r0 & rest & Hmem0 & Hb0 & Hlo0 & Hhi0 & Hwlo0 & Hwhi0 & Hci0 & Hsk & S1 & S2 & S3 & S4 &
  Hat & Hwf2 & Hnc2 & Hma2 & Hra & Hra2 & Hk33).
pose proof HEF as (E2 & _ & _).
pose proof HPI as ((HAR & Hsb & Hpb & Hfr & Hpm) & (b & HSNK) & HoM).
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = w64 (sp0 + OSP_FW)) by exact (regsT_sp E ss ms OSP_FW HS E2 S2).
assert (R3 : getr regsT 3 = w64 (as_gp B)) by (rewrite (regsT_gt E ss ms 3 3 HS HEF) by (reflexivity || lia || exact S3); apply HR).
assert (R4 : getr regsT 4 = w64 (as_tp B)) by (rewrite (regsT_gt E ss ms 4 4 HS HEF) by (reflexivity || lia || exact S4); apply HR).
assert (R10 : getr regsT 10 = w64 x) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS); exact H10).
assert (R11 : getr regsT 11 = w64 (Z.of_nat (length bs))) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS); exact H11).
assert (R12 : getr regsT 12 = w64 (sp0 + FO)) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 12 HS), S12; cbn [sv_denot]; rewrite E2; reflexivity).
eapply SRr_bind.
{ eapply (kcall W E ss ms md sp0 SNK_STK r0 rest k ra OSP_FW IBO (IBO + 80) (SNK_STK + OSP_FW) (fw_xw sp0 D M)
    (fun _ mem2 md2 => PI (out ++ bs) mem2 md2) HS Hrv E2 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0 S1 S2 Hat Hwf2 Hnc2 Hma2 Hci0).
  - unfold SNK_STK, OSP_FW. lia.
  - unfold SNK_STK, OSP_FW. lia.
  - unfold OSP_FW. lia.
  - geo. lia.
  - geo. lia.
  - intros a Hx Ha. unfold fw_xw in Hx. geo. lia.
  - intros r a Hr Ha. destruct (rest_away a (rest_ext E rest r a Hsk HEF Hr Ha)) as (Hr64 & Hb & Hx).
    split; [exact Hr64|]. split; [unfold SNK_STK, OSP_FW in *; lia | exact Hx].
  - intros r a Hr Ha. exfalso. exact (rest_win E rest r a Hsk Hr Ha).
  - intros a Ha. apply Hpb. unfold snk_band. lia.
  - rewrite Hpc. eapply SRr_mono.
    { apply (AFWX ly S U W regsT (ms_mem ms) md sp0 D N M out b x bs (pi_base out (ms_mem ms) md HPI)
        ltac:(split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; exact Hra2 | split; [exact R2 | split; [exact R3 | exact R4]]])
        R10 R11 R12 HSNK (pi_dest out (ms_mem ms) md HPI) Hsrc ltac:(lia)). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & (HA2 & Hsb2 & Hpb2 & Hfr2 & Hpm2) & HQ2 & H102 & (b2 & HSNK2)).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [unfold cfg_at, raZ; rewrite R1; rewrite unsigned_lit_small by lia; reflexivity|].
    split; [exact HQ2|]. split; [exact Hsb2|].
    split; [intros a Hr Hb Hx; apply Hfr2; [exact Hr | unfold SNK_STK, OSP_FW in *; lia | exact Hx]|].
    split; [exact Hpm2|].
    split; [|split; [exists b2; exact HSNK2 | rewrite length_app, Nat2Z.inj_add; lia]].
    split; [exact HA2|]. split; [eapply same_but_materialized_trans; [exact Hsb | exact Hsb2]|].
    split; [exact Hpb2|]. split.
    + intros a Hr Hb Hx. rewrite Hfr2; [exact (Hfr a Hr Hb Hx) | exact Hr | geo; lia | exact Hx].
    + intros a Hp. exact (Hpm2 a (Hpm a Hp)). }
cbv beta. intros W' c' _ (-> & ms2 & mat2 & -> & HS2 & HQ2 & Hfr2 & Hpm2 & HQ).
apply (HK (havoc E k (map (getr (ms_regs ms2)) CLOB))). split; [exact HS2|]. split; [apply kafter_resv; rewrite Hmem0; discriminate|].
split; [exact HQ|]. split; [exact (EF_havoc E k _ HEF Hk33) | exact (A_havoc E k _ A HA HAk)].
Qed.
(* ---- the sources __fwritex copies ---- *)
Lemma cstr_byte : forall (mem : word -> option byte) p s i, cstr tfibsegs W mem p s -> 0 <= i <= Z.of_nat (length s) ->
  aview tfibsegs (w_H W) mem (p + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0) /\ 0 <= nth (Z.to_nat i) (s ++ [0]) 0 < 256.
Proof.
intros mem p s i (Hg & _) Hi. destruct (Hg (Z.to_nat i) ltac:(rewrite length_app; cbn; lia)) as (Hv & Hr).
split; [|exact Hr]. pose proof (Hv 0%nat ltac:(lia)) as Hb. rewrite Z.add_0_r, Z2Nat.id in Hb by lia.
unfold aview. rewrite Hb. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte.
change (Z.of_nat 1) with 1. change (Z.of_nat 0) with 0. rewrite Z.mul_0_r, Z.shiftr_0_r. unfold bv_wrap.
change (bv_modulus 8) with 256. change (2 ^ (8 * 1)) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma amem_sub : forall x n n', amem_range x n -> 0 <= n' <= n -> amem_range x n'.
Proof. intros x n n' H Hn. unfold amem_range in *. lia. Qed.
(* a string or a window of the format: its bytes, addressability and the room it leaves, in the current memory *)
Lemma fw_src_win : forall out mem md x (l : list Z) o bs,
  PI out mem md -> cstr_ok tfibsegs W mem0 x l -> (forall a, x <= a < x + Z.of_nat (length l) + 1 -> ~ (D <= a < D + M)) ->
  (o + length bs <= length l)%nat -> firstn (length bs) (skipn o l) = bs -> fw_src W mem D M (x + Z.of_nat o) bs.
Proof.
intros out mem md x l o bs H Hc Hd Ho Hbs. pose proof Hc as (Hcs & H4096 & Hac & H40 & Ham & Hra & Hhu & _).
assert (Hl : forall i, 0 <= i < Z.of_nat (length bs) -> nth (Z.to_nat i) bs 0 = nth (o + Z.to_nat i) l 0).
{ intros i Hi. rewrite <- Hbs at 1. rewrite nth_firstn. replace (Z.to_nat i <? length bs)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. reflexivity. }
unfold fw_src. split; [lia|]. split; [lia|]. split.
{ destruct (Z_lt_le_dec (x + Z.of_nat o) D) as [L|L].
  - left. destruct (Z_lt_le_dec (x + Z.of_nat o + Z.of_nat (length bs)) (D + 1)) as [L2|L2]; [lia|].
    exfalso. apply (Hd D); [lia | geo; lia].
  - right. destruct (Z_lt_le_dec (x + Z.of_nat o) (D + M)) as [L2|L2]; [|exact L2]. exfalso. apply (Hd (x + Z.of_nat o)); lia. }
split.
{ intros i Hi. rewrite (pi_view out mem md (x + Z.of_nat o + i) H) by (try (geo; lia); apply Hd; lia).
  replace (x + Z.of_nat o + i) with (x + Z.of_nat (o + Z.to_nat i)) by lia.
  destruct (cstr_byte mem0 x l (Z.of_nat (o + Z.to_nat i)) Hcs ltac:(lia)) as (Hb & _). rewrite Hb, Hl by exact Hi.
  rewrite Nat2Z.id. rewrite app_nth1 by lia. reflexivity. }
split.
{ apply Forall_forall. intros z Hz. apply In_nth with (d := 0) in Hz as (j & Hj & <-).
  assert (Hj' : (o + j < length l)%nat) by lia.
  assert (Hn : nth j bs 0 = nth (o + j) l 0) by (pose proof (Hl (Z.of_nat j) ltac:(lia)) as X; rewrite Nat2Z.id in X; exact X).
  rewrite Hn.
  destruct (cstr_byte mem0 x l (Z.of_nat (o + j)) Hcs ltac:(lia)) as (_ & Hr).
  rewrite Nat2Z.id, app_nth1 in Hr by lia. exact Hr. }
split; [unfold amem_range in *; lia|].
split.
{ apply (pi_ra out mem md _ _ H); [lia | geo; lia |]. intros y Hy. apply Hra. lia. }
intros Hb0. apply (pi_hull out mem md _ _ H); [lia | geo; lia | exact Hb0 |].
intros s0 Hs0. apply Hhu. unfold shadow_addr in *.
assert ((SHADOW_OFF + (x + Z.of_nat o + Z.of_nat (length bs) - 1) / 8) / 8 <= (SHADOW_OFF + (x + (Z.of_nat (length l) + 1) - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert ((SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + (x + Z.of_nat o) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
lia.
Qed.
Lemma rom_off_dest : forall x n, 0x10000 <= x -> x + n <= 0x30000 -> forall a, x <= a < x + n -> ~ (D <= a < D + M).
Proof.
intros x n H1 H2 a Ha Hd. destruct HD as (_ & _ & _ & _ & HDb & _). destruct (HDb a Hd) as (_ & _ & Hno).
apply Hno. apply in_rom_seg0. lia.
Qed.
Lemma str_off_dest : forall p s, cstr_ok tfibsegs W mem0 p s -> (p + Z.of_nat (length s) + 1 <= D \/ D + N <= p) ->
  forall a, p <= a < p + Z.of_nat (length s) + 1 -> ~ (D <= a < D + M).
Proof. intros p s _ Hd a Ha Hx. lia. Qed.
Lemma fw_src_rom0 : forall mem x, 0x10000 <= x < 0x30000 -> fw_src W mem D M x [].
Proof.
intros mem x Hx. pose proof (rom_off_dest x 1 ltac:(lia) ltac:(lia) x ltac:(lia)) as Hd.
unfold fw_src. cbn [length Z.of_nat]. split; [lia|]. split; [geo; lia|]. split; [lia|]. split; [intros i Hi; lia|].
split; [constructor|]. split; [unfold amem_range; geo; lia|]. split; [intros y Hy; lia | intros Hl; lia].
Qed.
(* ---- strnlen through the interceptor ---- *)
Lemma unp_high' : forall (m : word -> option byte) md1 a, ARU tfibsegs B ly S U W m md1 -> kHighMemBeg <= a < 2 ^ 64 ->
  unpoison U m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros m md1 a HA Ha. apply unpoison_out. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [|reflexivity].
exfalso. pose proof (ush_facts tfibsegs B ly S U W m md1 _ HA Ei) as (_ & _ & L2).
rewrite unsigned_lit_small in L2 by (unfold kHighMemBeg in Ha; lia). unfold kHighMemBeg in *. lia.
Qed.
Lemma pi_rom : forall out mem md, PI out mem md -> rom_viewN tfibsegs B W mem.
Proof.
intros out mem md H a Ha Hno Her. pose proof (tfib_rom_low a Ha) as Hl.
assert (Hd : ~ (D <= a < D + M)) by (intros Hd; destruct HD as (_ & _ & _ & _ & HDb & _); destruct (HDb a Hd) as (_ & _ & Hro); exact (Hro Ha)).
rewrite (pi_view out mem md a H) by (try exact Hd; geo; lia).
exact (HRV a Ha Hno Her).
Qed.
Lemma pi_ecall : forall out mem md regs, PI out mem md -> YK0s.ret_ok (getr regs 1) -> spZ regs = sp0 + OSP_FW ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> ecall_preU tfibsegs B ly S U W regs mem md.
Proof.
intros out mem md regs H Hra Hsp H3 H4. pose proof H as ((HA & _ & Hpb & _ & _) & _).
split; [|split; [exact (ARU_ok tfibsegs B ly S U W _ md HA) | exact (ARU_poisoned tfibsegs B ly S U W _ md HA)]].
split; [exact (ARU_AR tfibsegs B ly S U W _ md HA)|]. split; [exact Hra|]. rewrite Hsp.
split; [geo; rewrite Z.add_mod, G3 by lia; reflexivity|]. split; [geo; unfold ESTACK; lia|]. split; [geo; lia|].
split; [|split; [exact H3 | exact H4]].
intros a Ha. destruct (Hpb a ltac:(unfold snk_band; geo; unfold ESTACK in Ha; lia)) as [Hh [bb Hbb]]. split; [exact Hh|]. exists bb.
rewrite (unp_high' mem md a HA) by (geo; unfold ESTACK in Ha; lia). exact Hbb.
Qed.
(* the frame a strnlen call keeps: only its window [sp0 - 9104, sp0 - 912) changes *)
Lemma pi_snl : forall out mem md mem' md', PI out mem md -> ARU tfibsegs B ly S U W mem' md' -> same_but_materialized md md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + OSP_FW - 2 * ESTACK <= a < sp0 + OSP_FW) ->
    aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) -> PI out mem' md'.
Proof.
intros out mem md mem' md' ((HA & Hsb & Hpb & Hfr & Hpm) & (b & HS) & HoM) HA2 Hsb2 Hfr2 Hpm2.
split; [|split; [exists b; apply (SNK_xfer mem mem' out b HS HoM); intros a Ha; unfold snk_cell in Ha; apply Hfr2; geo; unfold ESTACK; lia | exact HoM]].
split; [exact HA2|]. split; [eapply same_but_materialized_trans; [exact Hsb | exact Hsb2]|].
split; [intros a Ha; apply Hpm2; apply Hpb; exact Ha|]. split.
- intros a Hr Hb Hx. rewrite Hfr2; [exact (Hfr a Hr Hb Hx) | exact Hr | geo; unfold ESTACK; lia].
- intros a Hp. exact (Hpm2 a (Hpm a Hp)).
Qed.
(* a call of the strnlen interceptor; the contract instance is handed in as HC *)
Lemma step_snl_gen : forall A out E ss ms md k ra p n kv Q,
  WS A out E ss ms md -> ss_pc ss = W_STRNLEN -> callchk k ra OSP_FW 0 0 ss = true ->
  sv_denot E (sr_get (ss_regs ss) 10%bv) = w64 p -> sv_denot E (sr_get (ss_regs ss) 11%bv) = w64 n ->
  forallb (fun p => (fst p <? k)%nat) A = true ->
  (forall regs, getr regs 1 = Z_to_bv 64 ra -> spZ regs = sp0 + OSP_FW -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
     getr regs 10 = w64 p -> getr regs 11 = w64 n -> YK0s.ret_ok (getr regs 1) ->
     SRr tfibsegs W (cfg_at tfibsegs W_STRNLEN regs (ms_mem ms) md)
       (fun W' c' => W' = W /\ exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
          ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
          getr regs' 10 = w64 kv /\
          (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
          (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a))) ->
  (forall E' ms' md', WS A out E' (kafter k ss ra OSP_FW 0 0) ms' md' -> (forall i, (i < k)%nat -> ew E' i = ew E i) ->
     ew E' (k + 4)%nat = getr (ms_regs ms') 10 -> getr (ms_regs ms') 10 = w64 kv -> SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros A out E ss ms md k ra p n kv Q (HS & Hrv & HPI & HEF & HA) Hpc Hck H10 H11 HAk HC HK.
destruct (callchk_sound _ _ _ _ _ _ Hck) as (r0 & rest & Hmem0 & Hb0 & Hlo0 & Hhi0 & Hwlo0 & Hwhi0 & Hci0 & Hsk & S1 & S2 & S3 & S4 &
  Hat & Hwf2 & Hnc2 & Hma2 & Hra & Hra2 & Hk33).
pose proof HEF as (E2 & _ & _). pose proof HPI as ((HAR & Hsb & Hpb & Hfr & Hpm) & _ & _).
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = w64 (sp0 + OSP_FW)) by exact (regsT_sp E ss ms OSP_FW HS E2 S2).
assert (HspT : spZ regsT = sp0 + OSP_FW) by (unfold spZ; rewrite R2; apply unsigned_lit_small; geo; lia).
assert (R3 : getr regsT 3 = w64 (as_gp B)) by (rewrite (regsT_gt E ss ms 3 3 HS HEF) by (reflexivity || lia || exact S3); apply HR).
assert (R4 : getr regsT 4 = w64 (as_tp B)) by (rewrite (regsT_gt E ss ms 4 4 HS HEF) by (reflexivity || lia || exact S4); apply HR).
assert (R10 : getr regsT 10 = w64 p) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS); exact H10).
assert (R11 : getr regsT 11 = w64 n) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS); exact H11).
assert (Rok : YK0s.ret_ok (getr regsT 1)) by (rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; exact Hra2).
eapply SRr_bind.
{ eapply (kcall W E ss ms md sp0 SNK_STK r0 rest k ra OSP_FW 0 0 (2 * ESTACK) (fun _ => False)
    (fun regs2 mem2 md2 => PI out mem2 md2 /\ getr regs2 10 = w64 kv) HS Hrv E2 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0 S1 S2 Hat Hwf2 Hnc2 Hma2 Hci0).
  - unfold ESTACK. lia.
  - unfold SNK_STK, OSP_FW, ESTACK. lia.
  - unfold OSP_FW. lia.
  - geo. lia.
  - geo. lia.
  - intros a Hx. contradiction.
  - intros r a Hr Ha. destruct (rest_away a (rest_ext E rest r a Hsk HEF Hr Ha)) as (Hr64 & Hb & _).
    split; [exact Hr64|]. split; [unfold SNK_STK, OSP_FW, ESTACK in *; lia | intros []].
  - intros r a Hr Ha. exfalso. exact (rest_win E rest r a Hsk Hr Ha).
  - intros a Ha. apply Hpb. unfold snk_band. lia.
  - rewrite Hpc. eapply SRr_mono; [apply (HC regsT R1 HspT R3 R4 R10 R11 Rok)|].
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HA2 & HQ2 & Hsb2 & H102 & Hfr2 & Hpm2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [unfold cfg_at, raZ; rewrite R1; rewrite unsigned_lit_small by lia; reflexivity|].
    split; [exact HQ2|]. split; [exact Hsb2|].
    split; [intros a Hr Hb _; apply Hfr2; [exact Hr | rewrite HspT; exact Hb]|].
    split; [exact Hpm2|]. split; [|exact H102].
    apply (pi_snl out (ms_mem ms) md mem2 md2 HPI HA2 Hsb2); [|exact Hpm2].
    intros a Hr Hb. apply Hfr2; [exact Hr | rewrite HspT; exact Hb]. }
cbv beta. intros W' c' _ (-> & ms2 & mat2 & -> & HS2 & HQ2 & Hfr2 & Hpm2 & HQ & HQ10).
apply (HK (havoc E k (map (getr (ms_regs ms2)) CLOB))).
- split; [exact HS2|]. split; [apply kafter_resv; rewrite Hmem0; discriminate|].
  split; [exact HQ|]. split; [exact (EF_havoc E k _ HEF Hk33) | exact (A_havoc E k _ A HA HAk)].
- intros i Hi. apply ew_havoc_old. exact Hi.
- rewrite (ew_havoc_new E k _ 4 (Z_to_bv 64 0)) by (cbn; lia). reflexivity.
- exact HQ10.
Qed.
(* a string byte in the current memory *)
Lemma str_cur : forall out mem md p s i, PI out mem md -> cstr_ok tfibsegs W mem0 p s ->
  (p + Z.of_nat (length s) + 1 <= D \/ D + N <= p) -> 0 <= i <= Z.of_nat (length s) ->
  aview tfibsegs (w_H W) mem (p + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0).
Proof.
intros out mem md p s i H Hc Hd Hi. pose proof Hc as (Hcs & H4096 & Hac & _).
rewrite (pi_view out mem md (p + i) H) by (try (geo; lia); lia).
exact (proj1 (cstr_byte mem0 p s i Hcs Hi)).
Qed.
Lemma str_nz : forall p s i, cstr_ok tfibsegs W mem0 p s -> 0 <= i < Z.of_nat (length s) -> nth (Z.to_nat i) (s ++ [0]) 0 <> 0.
Proof.
intros p s i ((_ & Hnz) & _) Hi. rewrite app_nth1 by lia. rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. lia.
Qed.
Lemma str_ecall_facts : forall out mem md p s regs, PI out mem md -> cstr_ok tfibsegs W mem0 p s ->
  (p + Z.of_nat (length s) + 1 <= D \/ D + N <= p) -> spZ regs = sp0 + OSP_FW ->
  (forall n, 0 <= n <= Z.of_nat (length s) + 1 -> src_ok tfibsegs W regs mem p n) /\
  (forall a, p <= a <= p + Z.of_nat (length s) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
  (forall n, 0 <= n <= Z.of_nat (length s) + 1 -> amem_range p n) /\
  (forall n, 0 <= n <= Z.of_nat (length s) + 1 -> range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n) /\
  (forall n, 0 < n <= Z.of_nat (length s) + 1 -> shadow_hull_vis (aview tfibsegs (w_H W) mem) p n) /\
  (forall a, p + Z.of_nat (length s) < a < p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 ->
     aview tfibsegs (w_H W) mem a <> None) /\
  mconsts_view W mem.
Proof.
intros out mem md p s regs H Hc Hd Hsp. pose proof Hc as (Hcs & H4096 & Hac & H40 & Ham & Hra & Hhu & Htl).
split; [|split; [|split; [|split; [|split; [|split]]]]].
- intros n Hn a Ha. split; [|rewrite Hsp; geo; unfold ESTACK; lia].
  replace a with (p + (a - p)) by lia. rewrite (str_cur out mem md p s (a - p) H Hc Hd) by lia. discriminate.
- intros a Ha. rewrite Hsp. geo. unfold ESTACK. lia.
- intros n Hn. unfold amem_range in *. lia.
- intros n Hn. apply (pi_ra out mem md _ _ H); [lia | geo; lia |]. intros y Hy. apply Hra. lia.
- intros n Hn. apply (pi_hull out mem md _ _ H); [lia | geo; lia | lia |]. intros s0 Hs0. apply Hhu. unfold shadow_addr in *.
  assert ((SHADOW_OFF + (p + n - 1) / 8) / 8 <= (SHADOW_OFF + (p + (Z.of_nat (length s) + 1) - 1) / 8) / 8)
    by (apply Z.div_le_mono; [lia|]; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  lia.
- intros a Ha. apply (pi_vis out mem md a H). apply Htl. exact Ha.
- apply (mconsts_of_rom_viewN B W mem TB). exact (pi_rom out mem md H).
Qed.
Lemma step_snl : forall A out E ss ms md k ra p s Q,
  WS A out E ss ms md -> ss_pc ss = W_STRNLEN -> callchk k ra OSP_FW 0 0 ss = true ->
  sv_denot E (sr_get (ss_regs ss) 10%bv) = w64 p -> sr_get (ss_regs ss) 11%bv = SLit 2147483647 ->
  cstr_ok tfibsegs W mem0 p s -> (p + Z.of_nat (length s) + 1 <= D \/ D + N <= p) -> Z.of_nat (length s) <= 2 ^ 30 ->
  forallb (fun p => (fst p <? k)%nat) A = true ->
  (forall E' ms' md', WS (((k + 4)%nat, Z.of_nat (length s)) :: A) out E'
     (YE3h.vf_add_fact (kafter k ss ra OSP_FW 0 0) (k + 4) (mkAF 0 (2 ^ 30) 0)) ms' md' -> SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros A out E ss ms md k ra p s Q HW Hpc Hck H10 S11 Hc Hd Hl HAk HK.
pose proof HW as (HS & Hrv & HPI & HEF & HA). pose proof Hc as (Hcs & H4096 & Hac & _).
apply (step_snl_gen A out E ss ms md k ra p 2147483647 (Z.of_nat (length s)) Q HW Hpc Hck H10 ltac:(rewrite S11; reflexivity) HAk).
- intros regs R1 Hsp R3 R4 R10 R11 Rok.
  destruct (str_ecall_facts out (ms_mem ms) md p s regs HPI Hc Hd Hsp) as (Fsrc & Fwin & Fam & Fra & Fhu & Ftl & Fmc).
  apply (ASNL ly S U W regs (ms_mem ms) md p 2147483647 (Z.of_nat (length s)) (pi_ecall out (ms_mem ms) md regs HPI Rok Hsp R3 R4)).
  + rewrite Hsp. geo. unfold ESTACK. lia.
  + intros a Ha. destruct HPI as ((_ & _ & Hpb & _) & _). apply Hpb. unfold snk_band. rewrite Hsp in Ha. geo. unfold ESTACK in Ha. lia.
  + exact R10. + exact R11. + lia. + lia. + lia. + lia. + lia. + geo. lia.
  + split; [lia|]. split.
    * intros i Hi. exists (nth (Z.to_nat i) (s ++ [0]) 0). split; [exact (str_cur out (ms_mem ms) md p s i HPI Hc Hd ltac:(lia)) | exact (str_nz p s i Hc Hi)].
    * intros _. rewrite (str_cur out (ms_mem ms) md p s _ HPI Hc Hd) by lia. rewrite Nat2Z.id, app_nth2, Nat.sub_diag by lia. reflexivity.
  + apply Fsrc. lia.
  + exact Fwin.
  + apply Fam. lia.
  + apply Fra. lia.
  + apply Fhu. lia.
  + exact Ftl.
  + exact Fmc.
- intros E' ms' md' (HS' & Hrv' & HPI' & HEF' & HA') Hag H84 H10'.
  apply (HK E' ms' md'). split; [|split; [exact Hrv' | split; [exact HPI' | split; [exact HEF'|]]]].
  + apply YE3h.st_ok_add_fact; [exact HS' | exact Hrv' |]. rewrite H84, H10'. rewrite unsigned_lit_small by lia. lia.
  + constructor; [|exact HA']. cbn [fst snd]. rewrite H84, H10'. apply unsigned_lit_small. lia.
Qed.
Lemma step_snln : forall A out E ss ms md k k2 ra p s j kv Q,
  WS A out E ss ms md -> ss_pc ss = W_STRNLEN -> callchk k ra OSP_FW 0 0 ss = true ->
  sv_denot E (sr_get (ss_regs ss) 10%bv) = w64 p -> sr_get (ss_regs ss) 11%bv = SOff j 0 -> (j < k)%nat ->
  bv_unsigned (ew E j) = kv -> 1 <= kv <= Z.of_nat (length s) ->
  cstr_ok tfibsegs W mem0 p s -> (p + Z.of_nat (length s) + 1 <= D \/ D + N <= p) -> kv <= 2 ^ 30 ->
  forallb (fun p => (fst p <? k)%nat) A = true -> ss_atoms_lt k2 (kafter k ss ra OSP_FW 0 0) = true ->
  (forall E' ms' md', WS A out E' (set_regs_pc (kafter k ss ra OSP_FW 0 0) [((10%bv : bv 5), SOff j 0)] ra) ms' md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros A out E ss ms md k k2 ra p s j kv Q HW Hpc Hck H10 S11 Hj Hkv Hkb Hc Hd Hl HAk Hat2 HK.
pose proof HW as (HS & Hrv & HPI & HEF & HA). pose proof Hc as (Hcs & H4096 & Hac & _).
apply (step_snl_gen A out E ss ms md k ra p kv kv Q HW Hpc Hck H10
  ltac:(rewrite S11; cbn [sv_denot]; rewrite Hkv, Z.add_0_r; reflexivity) HAk).
- intros regs R1 Hsp R3 R4 R10 R11 Rok.
  destruct (str_ecall_facts out (ms_mem ms) md p s regs HPI Hc Hd Hsp) as (Fsrc & Fwin & Fam & Fra & Fhu & Ftl & Fmc).
  apply (ASNLN ly S U W regs (ms_mem ms) md p kv (pi_ecall out (ms_mem ms) md regs HPI Rok Hsp R3 R4)).
  + rewrite Hsp. geo. unfold ESTACK. lia.
  + intros a Ha. destruct HPI as ((_ & _ & Hpb & _) & _). apply Hpb. unfold snk_band. rewrite Hsp in Ha. geo. unfold ESTACK in Ha. lia.
  + exact R10. + exact R11. + lia. + lia. + geo. lia.
  + split; [lia|]. split.
    * intros i Hi. exists (nth (Z.to_nat i) (s ++ [0]) 0). split; [exact (str_cur out (ms_mem ms) md p s i HPI Hc Hd ltac:(lia)) | exact (str_nz p s i Hc ltac:(lia))].
    * intros Hx. lia.
  + apply Fsrc. lia.
  + intros a Ha. apply Fwin. lia.
  + apply Fam. lia.
  + apply Fra. lia.
  + apply Fhu. lia.
  + exact Fmc.
- intros E' ms' md' (HS' & Hrv' & HPI' & HEF' & HA') Hag H84 H10'.
  apply (HK E' ms' md'). split; [|split; [unfold set_regs_pc; exact Hrv' | split; [exact HPI' | split; [exact HEF' | exact HA']]]].
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E' _ _ HS' Hrv') as Hshape.
  destruct (callchk_sound _ _ _ _ _ _ Hck) as (r0 & rest & Hmem0 & _).
  assert (Hpc2 : ss_pc (kafter k ss ra OSP_FW 0 0) = ra) by (unfold kafter; rewrite Hmem0; reflexivity).
  rewrite Hpc2 in Hshape. rewrite Hshape. rewrite Hshape in HS'. rewrite restrict_mkst_fx in HS' |- *.
  apply (st_ok_set_regs tfibsegs k2 E' E' _ _ _ _ ra _ _ HS' (YP06.env_agree_refl k2 E') Hat2 Hrv').
  + reflexivity.
  + intros r _. reflexivity.
  + constructor; [|constructor]. cbn [fst snd]. split; [reflexivity|]. rewrite H10'. cbn [sv_denot].
    rewrite (Hag j Hj), Hkv, Z.add_0_r. reflexivity.
Qed.
(* the NUL after a %s string (`if (p < 0 && *z)`, lbu at 0x8f898) *)
Lemma step_lbu : forall A out E ss ms md k p s Q,
  WS A out E ss ms md -> ss_pc ss = 0x8f898 -> ss_atoms_lt k ss = true ->
  sv_denot E (sr_get (ss_regs ss) 11%bv) = w64 (p + Z.of_nat (length s)) ->
  cstr_ok tfibsegs W mem0 p s -> (p + Z.of_nat (length s) + 1 <= D \/ D + N <= p) ->
  (forall ms' md', WS A out E (set_regs_pc ss [((12%bv : bv 5), SLit 0)] 0x8f89c) ms' md' -> SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros A out E ss ms md k p s Q (HS & Hrv & HPI & HEF & HA) Hpc Hat H11 Hc Hd HK.
pose proof Hc as (Hcs & H4096 & Hac & _).
assert (R11 : getr (ms_regs ms) 11 = Z_to_bv 64 (p + Z.of_nat (length s))) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS); exact H11).
assert (Hnul : aview tfibsegs (w_H W) (ms_mem ms) (p + Z.of_nat (length s)) = Some 0).
{ rewrite (str_cur out (ms_mem ms) md p s _ HPI Hc Hd) by lia. rewrite Nat2Z.id, app_nth2, Nat.sub_diag by lia. reflexivity. }
eapply SRr_bind; [apply (vf_lbu_nul W E ss ms md k (p + Z.of_nat (length s)) HS Hpc Hrv Hat R11 ltac:(geo; lia) Hnul)|].
cbv beta. intros W' c' _ (-> & ms1 & mat1 & -> & HS1 & Hm1).
apply HK. split; [exact HS1|]. split; [exact Hrv|]. split; [|exact (conj HEF HA)].
rewrite Hm1. apply (PI_run out (ms_mem ms) md (ms_mem ms) mat1 HPI); [intros; reflexivity|].
destruct HPI as ((_ & _ & Hpb & _) & _). exact Hpb.
Qed.
(* a branch the walk resolves by arithmetic *)
Lemma step_br : forall A out E ss ms md c a b Q,
  WS A out E ss ms md -> branch_taken c (sv_denot E a) (sv_denot E b) = false ->
  (WS A out E (YP06.add_cond ss (mkAC (neg_bc c) a b)) ms md -> SRr tfibsegs W (mkCfg ms md) Q) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros A out E ss ms md c a b Q (HS & Hrv & HPI & HEF & HA) Hb HK. apply HK.
split; [apply st_ok_add_cond_neg; assumption|]. split; [exact Hrv|]. split; [exact HPI|]. split; assumption.
Qed.
(* the return: back at ra with the frame apcore promises *)
Definition retchk (ss : sstate) : bool :=
  sv_eqb (sr_get (ss_regs ss) 1%bv) (SOff 1 0) && sv_eqb (sr_get (ss_regs ss) 2%bv) (SOff 2 OSP_PC) &&
  forallb (fun i => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat i))) (SOff i 0)) [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma ret_word : clookup tfibmusl_tbl 0x900a0 = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.
Lemma step_ret : forall A out E ss ms md v,
  WS A out E ss ms md -> ss_pc ss = 0x900a0 -> retchk ss = true ->
  sv_denot E (sr_get (ss_regs ss) 10%bv) = w64 v ->
  SRr tfibsegs W (mkCfg ms md)
    (snk_post B ly S U W regs0 mem0 md0 sp0 (sp0 + OSP_PC + 8) (fw_xw sp0 D M) v (fun mem' => exists b', SNK W mem' sp0 D N out b')).
Proof.
intros A out E ss ms md v (HS & Hrv & HPI & HEF & HA) Hpc Hck H10.
unfold retchk in Hck. apply andb_prop in Hck as [Hck Hf]. apply andb_prop in Hck as [S1 S2].
apply sv_eqb_eq in S1. apply sv_eqb_eq in S2. pose proof HEF as (E2 & _ & HE).
set (regsT := ms_regs ms).
assert (G : forall i, In i [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
  getr regsT (Z_to_bv 5 (Z.of_nat i)) = getr regs0 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. pose proof (proj1 (forallb_forall _ _) Hf i Hi) as Hs. apply sv_eqb_eq in Hs.
  assert (Hi32 : (i < 32)%nat /\ i <> 2%nat) by (cbn in Hi; lia).
  apply (regsT_gt E ss ms _ i HS HEF); [lia | lia | | exact Hs].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
assert (R1 : getr regsT 1 = getr regs0 1).
{ unfold regsT. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  apply (HE 1%nat 1%bv); [lia | lia | reflexivity]. }
assert (R2 : getr regsT 2 = getr regs0 2) by (unfold regsT; rewrite (regsT_sp E ss ms OSP_PC HS E2 S2); symmetry; apply HR).
apply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx_tfa W E ss ms md _ HS Hrv ltac:(rewrite Hpc; exact ret_word)).
intros mat'. split; [reflexivity|]. exists regsT, (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat' md).
split.
{ unfold cfg_at, raZ, w64. f_equal. f_equal. rewrite (R1 : getr (ms_regs ms) 1 = getr regs0 1). destruct HR as (Hok & _). unfold YK0s.ret_ok in Hok. rewrite Hok.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
pose proof (PI_run out (ms_mem ms) md (ms_mem ms) mat' HPI ltac:(intros; reflexivity)
  ltac:(destruct HPI as ((_ & _ & Hpb & _) & _); exact Hpb)) as (HF & HSNK & _).
split; [exact HF|]. split; [|split; [rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS); exact H10 | exact HSNK]].
intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [exact R2 | exact (G 3%nat ltac:(cbn; tauto)) | exact (G 4%nat ltac:(cbn; tauto))
  | exact (G 8%nat ltac:(cbn; tauto)) | exact (G 9%nat ltac:(cbn; tauto)) |].
assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]];
  [exact (G 18%nat ltac:(cbn; tauto)) | exact (G 19%nat ltac:(cbn; tauto)) | exact (G 20%nat ltac:(cbn; tauto))
  | exact (G 21%nat ltac:(cbn; tauto)) | exact (G 22%nat ltac:(cbn; tauto)) | exact (G 23%nat ltac:(cbn; tauto))
  | exact (G 24%nat ltac:(cbn; tauto)) | exact (G 25%nat ltac:(cbn; tauto)) | exact (G 26%nat ltac:(cbn; tauto))
  | exact (G 27%nat ltac:(cbn; tauto))].
Qed.
(* ---- small glue for the walks ---- *)
Lemma ws_drop : forall A out E ss ms md, WS A out E ss ms md -> WS A out E (pc_drop ss) ms md.
Proof.
intros A out E ss ms md (HS & Hrv & HPI & HEF & HA). split; [exact (st_ok_drop E ss _ HS)|].
split; [unfold pc_drop; exact Hrv|]. split; [exact HPI|]. split; assumption.
Qed.
Lemma ws_atom : forall A out E ss ms md j a, WS A out E ss ms md -> In (j, a) A -> bv_unsigned (ew E j) = a.
Proof. intros A out E ss ms md j a (_ & _ & _ & _ & HA) Hin. rewrite Forall_forall in HA. exact (HA (j, a) Hin). Qed.
Lemma ws_pi : forall A out E ss ms md, WS A out E ss ms md -> PI out (ms_mem ms) md.
Proof. intros A out E ss ms md (_ & _ & HPI & _). exact HPI. Qed.
Lemma ws_room : forall A out E ss ms md, WS A out E ss ms md -> Z.of_nat (length out) + 1 <= M.
Proof. intros A out E ss ms md (_ & _ & (_ & _ & H) & _). exact H. Qed.
Lemma fmt_off_dest : forall x (l : list Z), 0x10000 <= x -> x + Z.of_nat (length l) + 1 <= 0x30000 ->
  forall a, x <= a < x + Z.of_nat (length l) + 1 -> ~ (D <= a < D + M).
Proof. intros x l H1 H2 a Ha. apply (rom_off_dest x (Z.of_nat (length l) + 1)); lia. Qed.
Lemma fw_src_str : forall out mem md p s, PI out mem md -> cstr_ok tfibsegs W mem0 p s ->
  (p + Z.of_nat (length s) + 1 <= D \/ D + N <= p) -> fw_src W mem D M p s.
Proof.
intros out mem md p s H Hc Hd. pose proof (fw_src_win out mem md p s 0 s H Hc (str_off_dest p s Hc Hd) ltac:(lia)
  ltac:(rewrite skipn_O, firstn_all; reflexivity)) as X. rewrite Z.add_0_r in X. exact X.
Qed.
Lemma fw_src_strk : forall out mem md p s k, PI out mem md -> cstr_ok tfibsegs W mem0 p s ->
  (p + Z.of_nat (length s) + 1 <= D \/ D + N <= p) -> (k <= length s)%nat -> fw_src W mem D M p (firstn k s).
Proof.
intros out mem md p s k H Hc Hd Hk. assert (Hl : length (firstn k s) = k) by (rewrite length_firstn; lia).
pose proof (fw_src_win out mem md p s 0 (firstn k s) H Hc (str_off_dest p s Hc Hd) ltac:(lia)
  ltac:(rewrite skipn_O, Hl; reflexivity)) as X. rewrite Z.add_0_r in X. exact X.
Qed.
End w.
