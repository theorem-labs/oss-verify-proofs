(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL piece B2 (the separator): the stretch AFTER the
   ex_ws call, B 0x83ca8 (= exv_pc 0x77c) to the three cuts. Rule 24: proves no function (kind: segment lemma).
   THE CODE (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin, rows 481-516,
   530-531, 627-640): the shadow of q and of q + 8 (ASan slow paths B 0x841a0 / 0x841a8 unreachable: zero shadow of
   the real-stack cursor), end = in->end, p = in->p; `bgeu p, end` -> B 0x83d6c (s8 := 120(s1)) -> CX (s5 = -1);
   UBSan `beqz p` (B 0x83cc8) not taken (p >= 4096); the byte's shadow (B 0x83d2c the partial-granule path, back to
   B 0x83cdc; its report unreachable by the text's shadow); s8 := 120(s1); byte = ',': UBSan `beq p, -1` not taken, the
   store shadow of q (B 0x841b4 unreachable), 136(s1) += 1, 112(s1) += 56, in->p := p + 1, 128(s1) += 8, back to CL
   (exv_pc 0x534); else the closer test at B 0x83ef0 (shadow reloaded, B 0x8414c unreachable): byte <> 64(s1) -> CX
   (s5 = -1), byte = closer -> UBSan B 0x83f08 not taken, store shadow (B 0x84260 unreachable), in->p := p + 1,
   a1 = 136(s1) + 1 -> CC (exv_pc 0x9f8). Every UBSan / ASan arm is decided inside the symbolic run (facts on p, the
   shadow hints of [q, q + 40) and of the byte); each arm is ONE run to its cut (ExvB_Loop_B2_seat.v's conditions).
   Numerals: 0x77c, 0x534, 0x9f8, 0xa7c (DERIVED: cut / pc offsets, B address minus B's ex_value entry); 8, 16, 24,
   32, 40, 64, 96, 104, 112, 120, 128, 136, 144, 152, 176 (LENGTH: spill slots, struct ex fields); 44, 93, 125 (WORD:
   ASCII); 56 (LENGTH: pj node size); 2 ^ 64, 4096 (LENGTH: bounds); register numbers 11, 21-27 (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_kit ExvB_Loop_Stmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Open_kt ExvB_Loop_exw ExvB_Loop_B2_seat.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* the write windows of a run, all in the real stack: ex_value's frame slots and in->p *)
Ltac b2_awr U9 U19 :=
  lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply exw_awr_cons; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    rewrite ?U9, ?U19 in Ha; first [ lia | left; lia ] | ]);
  apply awr_ok_nil.
(* the environment after a run agrees with the seat's on the registers *)
Ltac b2_agree HEx :=
  rewrite HEx; split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity].
(* the pc literal of a cut *)
Ltac b2_pc off :=
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 ?z) _ _) _) _ =>
    replace (Z_to_bv 64 z) with (w64 (exv_pc off)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
(* a spill outside the run's write windows *)
Ltac b2_kspill K S :=
  unfold exv_spill; unfold exv_spill in S; eapply (exw_val_kept rsegs _ _ _ _ _ _); [|exact S];
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply K; lia.
Ltac b2_in := cbn [In]; repeat first [left; reflexivity | right].

Section p. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis KRUN : forall fx : YK11.FPState, KIT_RUNs (fx := fx) B ARx SK.
Hypothesis KOFS : forall fx : YK11.FPState, KIT_EXB_OF_S (fx := fx) B ARx SK.

(* EXB at the end of an arm: KIT_RUNs across the run (it writes only the frame slots and in->p), s8 = 120(s1) *)
Lemma b2_exb_end : forall (fx : YK11.FPState) E ly2 S2 Hp2 (W2 : world rsegs) (regs2 regs' : bvmap 5 word) mem2 md2
    mem' md' k pos,
  EXV_PRE B ARx E -> EXBs (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 k pos ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] ly2 S2 Hp2 W2 mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((exv_s1 E + 112 <= a < exv_s1 E + 144) \/ (e_q E <= a < e_q E + 8)) ->
     aview rsegs (w_H W2) mem' a = aview rsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem' a) ->
  exvl_P (e_mem E) mem' ->
  (forall r, In r b2_keep -> getr regs' r = getr regs2 r) ->
  getr regs' 24 = getr regs2 18 ->
  EXB (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs' mem' md' k pos.
Proof.
intros fx E ly2 S2 Hp2 W2 regs2 regs' mem2 md2 mem' md' k pos HP HBs HJ HK HG HM HR H24.
pose proof HBs as (regs0 & HB & HAG).
destruct (b2_geom B ARx SK HYP fx E ly2 S2 Hp2 W2 regs0 mem2 md2 k pos HP HB)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & _).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R18 & _).
apply (KOFS fx).
- apply (KRUN fx E ly2 S2 Hp2 W2 regs2 mem2 md2 k pos regs' mem' md' HP HBs HJ).
  + intros a Ha H1 H2 H3. apply HK; [exact Ha|]. lia.
  + exact HG.
  + exact HM.
  + intros r Hr Hr24. apply HR. unfold exv_bregs in Hr. unfold b2_keep.
    cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
      first [ exfalso; apply Hr24; reflexivity | b2_in ].
- rewrite H24, (HAG 18%bv ltac:(discriminate)). exact R18.
Qed.

(* the post-call stretch: from B 0x83ca8 with ex_ws's post (in->p at x0 + ip, past the whitespace) to the cuts *)
Definition b2_post (fx : YK11.FPState) (n : nat) (m : Z) : Prop :=
  forall E ly2 S2 Hp2 (W2 : world rsegs) (regs2 : bvmap 5 word) mem2 md2 k pos (c : Z) (i cap : nat)
    (acc : list (list Z * PjTree.jv)) (ip vv dlc : Z) (nm : list Z) (u : PjTree.jv),
  let o := (c =? 123) in
  let q := e_q E in
  e_n E = n -> EXV_PRE B ARx E -> EXBs (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 -> length acc = i ->
  prhex_cur W2 mem2 q (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  0 <= ip <= exv_len E -> (dlc = 0 \/ dlc = 1) -> Z.of_nat i < ip -> exv_len E - ip < m ->
  exv_V E =
    match skipn (Z.to_nat ip) (e_x E) with
    | c0 :: r1 =>
      if c0 =? 44 then exv_L (S (Z.to_nat (e_dep E))) o (S i) (exv_cap i cap) ((nm, u) :: acc) r1
      else if c0 =? PjGrammar.closer o then Some (PjGrammar.mk o (rev ((nm, u) :: acc)), r1)
      else None
    | [] => None
    end ->
  exv_dif E o vv dlc ((nm, u) :: acc) ->
  getr regs2 21 = w64 (-1) -> getr regs2 27 = w64 c ->
  getr regs2 22 = w64 (shadow_addr (q + 8)) -> getr regs2 23 = w64 (q + 8) ->
  exv_spills E W2 mem2 ly2 pos c vv i ->
  SRr rsegs W2 (cfg_at (fx := fx) rsegs (exv_pc 0x77c) regs2 mem2 md2) (EXV_POST B ARx SK E).

Lemma b2_post_ok : forall (fx : YK11.FPState) n m,
  CUT_CX (fx := fx) B ARx SK n -> CUT_CC (fx := fx) B ARx SK n -> CUT_CLm (fx := fx) B ARx SK n (m - 1) ->
  b2_post fx n m.
Proof.
intros fx n m HCX HCC HCL.
unfold CUT_CX in HCX. unfold CUT_CC in HCC. cbv zeta in HCC. unfold CUT_CLm in HCL. cbv zeta in HCL.
unfold b2_post. intros E ly2 S2 Hp2 W2 regs2 mem2 md2 k pos c i cap acc ip vv dlc nm u. cbv zeta.
intros Hn HPRE HBs Hi1 Hc1 Hc Hdep Hacc Hcur Hip Hdl Hii Hm HV Hdif H21 H27 H22 H23 HSP.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HBs as (regs0 & HB & HAG).
destruct (b2_geom B ARx SK HYP fx E ly2 S2 Hp2 W2 regs0 mem2 md2 k pos HPRE HB)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & GPRES & GAR).
pose proof HPRE as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PLEN & _).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & _ & _ & _
  & HSRC & _ & _ & _ & HQR & _).
destruct HSRC as (GT & Hx4 & Hxc & Hxam & Hxra & _).
pose proof Hcur as (Vq & Ve & Vdep & Vscr & Vdl).
pose proof HSP as HSP0.
destruct HSP0 as (S152 & S88 & S56 & S48 & S40 & S80 & S24 & S16 & S72 & S8 & S32 & S136 & S112 & S128 & S64 & S104
  & S96 & S120 & S144).
assert (Hi3 : Z.of_nat i <= exv_len E) by lia.
assert (Hlen0 : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.
remember (b2_env regs2 (e_x0 E + ip) (nth (Z.to_nat ip) (e_x E) 0) (e_x0 E + exv_len E)
  (if c =? 123 then 125 else 93) (Z.of_nat i)) as Ex eqn:HEx.
pose proof (b2_env_x regs2 (e_x0 E + ip) (nth (Z.to_nat ip) (e_x E) 0) (e_x0 E + exv_len E)
  (if c =? 123 then 125 else 93) (Z.of_nat i)) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
rewrite <- HEx in E32, E33, E34, E35, E36, E37, E38.
assert (ER : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew Ex nn = getr regs2 r)
  by (intros nn r Hr; rewrite HEx; exact (b2_env_reg _ _ _ _ _ _ nn r Hr)).
assert (E9 : ew Ex 9 = Z_to_bv 64 (exv_s1 E))
  by (rewrite (ER 9%nat 9%bv eq_refl), (HAG 9%bv ltac:(discriminate)); exact R9).
assert (E19 : ew Ex 19 = Z_to_bv 64 (e_q E))
  by (rewrite (ER 19%nat 19%bv eq_refl), (HAG 19%bv ltac:(discriminate)); exact R19).
assert (E25 : ew Ex 25 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ER 25%nat 25%bv eq_refl), (HAG 25%bv ltac:(discriminate)); exact R25).
assert (E18 : ew Ex 18 = getr regs2 18) by exact (ER 18%nat 18%bv eq_refl).
assert (Hcl : 93 <= (if c =? 123 then 125 else 93) <= 125) by (destruct (c =? 123); lia).
assert (Hx0 : 4096 <= e_x0 E /\ e_x0 E + exv_len E <= alloc_ceiling) by (rewrite Hlen0; lia).
assert (U9 : bv_unsigned (ew Ex 9) = exv_s1 E) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew Ex 19) = e_q E) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew Ex 32) = e_x0 E + ip) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew Ex 34) = e_x0 E + exv_len E) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew Ex 35) = (if c =? 123 then 125 else 93)) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew Ex 36) = Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew Ex 37) = 56 * Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew Ex 38) = 8 * Z.of_nat i) by (rewrite E38; apply unsigned_lit_small; lia).
pose (RUNTO := SRr_run_to_tok_AJx_inv (fx := fx) (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low
  B_prog_tbl B_prog_tbl_ok B_prog_wx (exvl_P (e_mem E)) (exvl_PLAW (e_mem E))).
unfold cfg_at. change (w64 (exv_pc 0x77c)) with (Z_to_bv 64 B2_PC).
(* the cursor cells the arms keep *)
assert (KCUR : forall (mem' : word -> option byte), (forall a, 0 <= a < 2 ^ 64 ->
    ~ ((exv_s1 E + 112 <= a < exv_s1 E + 144) \/ (e_q E <= a < e_q E + 8)) ->
    aview rsegs (w_H W2) mem' a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem') (e_q E + 8) 8 (e_x0 E + exv_len E) /\
  val_mem rsegs (mrestrict (w_H W2) mem') (e_q E + 16) 4 (e_dep E + 1) /\
  val_mem rsegs (mrestrict (w_H W2) mem') (e_q E + 24) 8 (e_scr E) /\
  val_mem rsegs (mrestrict (w_H W2) mem') (e_q E + 32) 4 dlc).
{ intros mem' K. split; [|split; [|split]].
  - apply (exw_val_kept rsegs (w_H W2) mem2 mem'); [|exact Ve].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply K; lia.
  - apply (exw_val_kept rsegs (w_H W2) mem2 mem'); [|exact Vdep].
    intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply K; lia.
  - apply (exw_val_kept rsegs (w_H W2) mem2 mem'); [|exact Vscr].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply K; lia.
  - apply (exw_val_kept rsegs (w_H W2) mem2 mem'); [|exact Vdl].
    intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply K; lia. }
destruct (Z_lt_le_dec ip (exv_len E)) as [Hlt | Hge].
2:{
(* ---- p = end: B 0x83cc4 taken, B 0x83d6c, CX with the grammar refusing ---- *)
assert (Hipe : ip = exv_len E) by lia.
assert (HSK : skipn (Z.to_nat ip) (e_x E) = []) by (apply skipn_all2; lia).
rewrite HSK in HV.
assert (HCS : conds_ok Ex [b2_cGE]).
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok, b2_cGE. cbn [ac_c ac_a ac_b].
  rewrite branch_geu_U, !U_SOff, U32, U34, !Z.add_0_r, !zcanon_id by (unfold M64; lia).
  apply negb_true_iff, Z.ltb_ge. lia. }
destruct (b2_seatB B ARx SK HYP fx E ly2 S2 Hp2 W2 regs2 regs0 mem2 md2 k pos c i vv ip Ex [b2_cGE]
  HPRE HB HAG H22 H23 Hc ltac:(lia) Hi3 Vq Ve HSP HEx HCS) as (HS & SHOK).
exw_run_to RUNTO HS HJ SHOK HPM B2_CX.
{ b2_awr U9 U19. }
exw_kept_of HFr (fun a => (exv_s1 E + 112 <= a < exv_s1 E + 144) \/ (e_q E <= a < e_q E + 8))
  ltac:(fun h => rewrite ?U9, ?U19 in h).
rename KEPT into K1.
lazymatch type of HS with st_ok _ ?Ex' _ _ =>
  assert (AG : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [e_x0 E + ip; nth (Z.to_nat ip) (e_x E) 0;
    e_x0 E + exv_len E; if c =? 123 then 125 else 93; Z.of_nat i; 56 * Z.of_nat i; 8 * Z.of_nat i])) Ex')
    by b2_agree HEx end.
assert (KR : forall r, In r b2_keep -> getr (ms_regs ms) r = getr regs2 r)
  by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs2 _ b2_keep HS AG ltac:(vm_compute; reflexivity) r Hr)).
prreg HS (24%bv : bv 5) RS8. cbn [ew ewset Nat.eqb] in RS8. rewrite E18 in RS8.
assert (HBE := b2_exb_end fx E ly2 S2 Hp2 W2 regs2 (ms_regs ms) mem2 md2 (ms_mem ms) _ k pos HPRE HBs HJ K1
  (fun a Ha => apresent_grows _ _ _ a HG Ha) HPM KR RS8).
pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 0 8 (SOff 32 0) (e_x0 E + ip) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(b2_in)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
destruct (KCUR (ms_mem ms) K1) as (Ve' & Vdep' & Vscr' & Vdl').
pmkst HS. b2_pc 0xa7c.
apply (HCX E ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) _ k pos (-1) Hn HPRE HBE).
- rewrite (KR 21%bv ltac:(b2_in)). exact H21.
- exists ip, (e_dep E + 1), dlc. split; [exact (conj VQ (conj Ve' (conj Vdep' (conj Vscr' Vdl'))))|].
  split; [exact Hdl|]. rewrite HV. split; [reflexivity|]. split; lia. }
(* ---- p < end: the byte at p ---- *)
destruct (skipn (Z.to_nat ip) (e_x E)) as [|c0 r1] eqn:SKP.
{ exfalso. pose proof (length_skipn (Z.to_nat ip) (e_x E)) as L. rewrite SKP in L. cbn [length] in L. lia. }
pose proof (exw_nth_skipn _ _ _ _ SKP) as Hc0.
pose proof (exw_skipn_S _ _ _ _ SKP) as Hr1.
assert (Hc8 : 0 <= c0 < 256).
{ destruct (GT (Z.to_nat ip) ltac:(lia)) as [_ R]. rewrite Hc0 in R. exact R. }
assert (U33 : bv_unsigned (ew Ex 33) = c0) by (rewrite E33, Hc0; apply unsigned_lit_small; lia).
assert (HLT : acond_ok Ex b2_cLT).
{ unfold acond_ok, b2_cLT. cbn [ac_c ac_a ac_b].
  rewrite branch_ltu_U, !U_SOff, U32, U34, !Z.add_0_r, !zcanon_id by (unfold M64; lia).
  apply Z.ltb_lt. lia. }
assert (HZ1 : Z.to_nat (ip + 1) = S (Z.to_nat ip)) by lia.
destruct (Z.eq_dec c0 44) as [H44 | H44].
{
(* ---- byte = ',': back to CL at i + 1 ---- *)
assert (HVc : exv_V E = exv_L (S (Z.to_nat (e_dep E))) (c =? 123) (S i) (exv_cap i cap) ((nm, u) :: acc) r1)
  by (rewrite HV, H44; reflexivity).
assert (HCS : conds_ok Ex [b2_cLT; b2_cEQ44]).
{ cbn [conds_ok]. split; [exact HLT|]. split; [|exact I]. unfold acond_ok, b2_cEQ44. cbn [ac_c ac_a ac_b].
  rewrite branch_eq_U, U_SOff, U33, Z.add_0_r, U_lit, zcanon_id by (unfold M64; lia). apply Z.eqb_eq. exact H44. }
destruct (b2_seatA B ARx SK HYP fx E ly2 S2 Hp2 W2 regs2 regs0 mem2 md2 k pos c i vv ip Ex [b2_cLT; b2_cEQ44]
  HPRE HB HAG H22 H23 Hc ltac:(lia) Hi3 Vq Ve HSP HEx HCS) as (HS & SHOK).
exw_run_to RUNTO HS HJ SHOK HPM B2_CL.
{ b2_awr U9 U19. }
exw_kept_of HFr (fun a => (exv_s1 E + 112 <= a < exv_s1 E + 144) \/ (e_q E <= a < e_q E + 8))
  ltac:(fun h => rewrite ?U9, ?U19 in h).
rename KEPT into K1.
lazymatch type of HS with st_ok _ ?Ex' _ _ =>
  assert (AG : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [e_x0 E + ip; nth (Z.to_nat ip) (e_x E) 0;
    e_x0 E + exv_len E; if c =? 123 then 125 else 93; Z.of_nat i; 56 * Z.of_nat i; 8 * Z.of_nat i])) Ex')
    by b2_agree HEx end.
assert (KR : forall r, In r b2_keep -> getr (ms_regs ms) r = getr regs2 r)
  by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs2 _ b2_keep HS AG ltac:(vm_compute; reflexivity) r Hr)).
prreg HS (24%bv : bv 5) RS8. cbn [ew ewset Nat.eqb] in RS8. rewrite E18 in RS8.
assert (HBE := b2_exb_end fx E ly2 S2 Hp2 W2 regs2 (ms_regs ms) mem2 md2 (ms_mem ms) _ k pos HPRE HBs HJ K1
  (fun a Ha => apresent_grows _ _ _ a HG Ha) HPM KR RS8).
pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 0 8 (SOff 32 1) (e_x0 E + ip + 1) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(b2_in)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
pose proof (exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RF. cbn [ms_mem restrict] in RF.
pose proof (exw_field rsegs _ _ 9%nat (exv_s1 E) _ _ _ _ _ 136 8 (SOff 36 1) (Z.of_nat i + 1) RF
  ltac:(cbn [ew ewset Nat.eqb]; exact U9) ltac:(b2_in)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U36; reflexivity) ltac:(cbn; lia) ltac:(zside)) as V136.
pose proof (exw_field rsegs _ _ 9%nat (exv_s1 E) _ _ _ _ _ 112 8 (SOff 37 56) (56 * Z.of_nat i + 56) RF
  ltac:(cbn [ew ewset Nat.eqb]; exact U9) ltac:(b2_in)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U37; reflexivity) ltac:(cbn; lia) ltac:(zside)) as V112.
pose proof (exw_field rsegs _ _ 9%nat (exv_s1 E) _ _ _ _ _ 128 8 (SOff 38 8) (8 * Z.of_nat i + 8) RF
  ltac:(cbn [ew ewset Nat.eqb]; exact U9) ltac:(b2_in)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U38; reflexivity) ltac:(cbn; lia) ltac:(zside)) as V128.
pose proof (exw_field rsegs _ _ 9%nat (exv_s1 E) _ _ _ _ _ 120 8 (SOff 18 0) (frame_addr ly2 1 pos) RF
  ltac:(cbn [ew ewset Nat.eqb]; exact U9) ltac:(b2_in)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E18, (HAG 18%bv ltac:(discriminate)), R18, Z.add_0_r;
        unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lia) ltac:(zside)) as V120.
destruct (KCUR (ms_mem ms) K1) as (Ve' & Vdep' & Vscr' & Vdl').
pose proof (st_ok_restrict_reg rsegs (w_H W2) _ _ _ 22%bv HS) as R22'.
lazymatch type of R22' with _ = sv_denot ?Ex' (sr_get ?l _) =>
  change (sr_get l 22%bv) with (b2_shx (SOff 19 8)) in R22';
  rewrite (b2_denot_shx Ex' 8 (e_q E) SHADOW_OFF ltac:(cbn [ew ewset Nat.eqb]; exact E19)
    ltac:(cbn [ew ewset Nat.eqb]; exact E25)) in R22' by (unfold SHADOW_OFF; lia) end.
cbn [ms_regs restrict] in R22'.
prreg HS (23%bv : bv 5) R23'. cbn [ew ewset Nat.eqb] in R23'. rewrite U19 in R23'.
pmkst HS. b2_pc 0x534.
apply (HCL E ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) _ k pos c (S i) (exv_cap i cap) ((nm, u) :: acc) (ip + 1) vv dlc
  Hn HPRE HBE Hi1 Hc1 Hc Hdep).
- cbn [length]. rewrite Hacc. reflexivity.
- refine (conj _ (conj Ve' (conj Vdep' (conj Vscr' Vdl')))). replace (e_x0 E + (ip + 1)) with (e_x0 E + ip + 1) by lia.
  exact VQ.
- lia.
- exact Hdl.
- lia.
- lia.
- rewrite HZ1, Hr1. exact HVc.
- exact Hdif.
- rewrite (KR 27%bv ltac:(b2_in)). exact H27.
- rewrite R22'. unfold w64, shadow_addr. reflexivity.
- rewrite R23'. reflexivity.
- b2_kspill K1 S152.
- b2_kspill K1 S88.
- b2_kspill K1 S56.
- b2_kspill K1 S48.
- b2_kspill K1 S40.
- b2_kspill K1 S80.
- b2_kspill K1 S24.
- b2_kspill K1 S16.
- b2_kspill K1 S72.
- b2_kspill K1 S8.
- b2_kspill K1 S32.
- unfold exv_spill. replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia. exact V136.
- unfold exv_spill. replace (56 * Z.of_nat (S i)) with (56 * Z.of_nat i + 56) by lia. exact V112.
- unfold exv_spill. replace (8 * Z.of_nat (S i)) with (8 * Z.of_nat i + 8) by lia. exact V128.
- b2_kspill K1 S64.
- b2_kspill K1 S104.
- b2_kspill K1 S96.
- exact V120.
- b2_kspill K1 S144. }
assert (HNE : acond_ok Ex b2_cNE44).
{ unfold acond_ok, b2_cNE44. cbn [ac_c ac_a ac_b].
  rewrite branch_ne_U, U_SOff, U33, Z.add_0_r, U_lit, zcanon_id by (unfold M64; lia).
  apply negb_true_iff, Z.eqb_neq. exact H44. }
assert (H44f : (c0 =? 44) = false) by (apply Z.eqb_neq; exact H44).
destruct (Z.eq_dec c0 (if c =? 123 then 125 else 93)) as [HCL0 | HCL0].
{
(* ---- byte = the closer: to CC ---- *)
assert (HVk : exv_V E = Some (PjGrammar.mk (c =? 123) (rev ((nm, u) :: acc)), r1)).
{ rewrite HV, H44f. unfold PjGrammar.closer. rewrite HCL0, Z.eqb_refl. reflexivity. }
assert (HCS : conds_ok Ex [b2_cLT; b2_cNE44; b2_cEQC]).
{ cbn [conds_ok]. split; [exact HLT|]. split; [exact HNE|]. split; [|exact I]. unfold acond_ok, b2_cEQC.
  cbn [ac_c ac_a ac_b].
  rewrite branch_eq_U, !U_SOff, U33, U35, !Z.add_0_r, !zcanon_id by (unfold M64; lia). apply Z.eqb_eq. exact HCL0. }
destruct (b2_seatA B ARx SK HYP fx E ly2 S2 Hp2 W2 regs2 regs0 mem2 md2 k pos c i vv ip Ex [b2_cLT; b2_cNE44; b2_cEQC]
  HPRE HB HAG H22 H23 Hc ltac:(lia) Hi3 Vq Ve HSP HEx HCS) as (HS & SHOK).
exw_run_to RUNTO HS HJ SHOK HPM B2_CC.
{ b2_awr U9 U19. }
exw_kept_of HFr (fun a => (exv_s1 E + 112 <= a < exv_s1 E + 144) \/ (e_q E <= a < e_q E + 8))
  ltac:(fun h => rewrite ?U9, ?U19 in h).
rename KEPT into K1.
lazymatch type of HS with st_ok _ ?Ex' _ _ =>
  assert (AG : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [e_x0 E + ip; nth (Z.to_nat ip) (e_x E) 0;
    e_x0 E + exv_len E; if c =? 123 then 125 else 93; Z.of_nat i; 56 * Z.of_nat i; 8 * Z.of_nat i])) Ex')
    by b2_agree HEx end.
assert (KR : forall r, In r b2_keep -> getr (ms_regs ms) r = getr regs2 r)
  by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs2 _ b2_keep HS AG ltac:(vm_compute; reflexivity) r Hr)).
prreg HS (24%bv : bv 5) RS8. cbn [ew ewset Nat.eqb] in RS8. rewrite E18 in RS8.
assert (HBE := b2_exb_end fx E ly2 S2 Hp2 W2 regs2 (ms_regs ms) mem2 md2 (ms_mem ms) _ k pos HPRE HBs HJ K1
  (fun a Ha => apresent_grows _ _ _ a HG Ha) HPM KR RS8).
pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 0 8 (SOff 32 1) (e_x0 E + ip + 1) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(b2_in)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
destruct (KCUR (ms_mem ms) K1) as (Ve' & Vdep' & Vscr' & Vdl').
prreg HS (11%bv : bv 5) R11'. cbn [ew ewset Nat.eqb] in R11'. rewrite U36 in R11'.
pmkst HS. b2_pc 0x9f8.
apply (HCC E ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) _ k pos c ((nm, u) :: acc) (ip + 1) vv dlc Hn HPRE HBE Hc Hdep).
- refine (conj _ (conj Ve' (conj Vdep' (conj Vscr' Vdl')))). replace (e_x0 E + (ip + 1)) with (e_x0 E + ip + 1) by lia.
  exact VQ.
- lia.
- exact Hdl.
- rewrite HZ1, Hr1. exact HVk.
- exact Hdif.
- rewrite R11'. cbn [length]. rewrite Hacc. unfold w64. f_equal. lia.
- b2_kspill K1 S152.
- b2_kspill K1 S96.
- b2_kspill K1 S104. }
(* ---- any other byte: CX with the grammar refusing ---- *)
assert (HVx : exv_V E = None).
{ rewrite HV, H44f. unfold PjGrammar.closer. rewrite (proj2 (Z.eqb_neq _ _) HCL0). reflexivity. }
assert (HCS : conds_ok Ex [b2_cLT; b2_cNE44; b2_cNEC]).
{ cbn [conds_ok]. split; [exact HLT|]. split; [exact HNE|]. split; [|exact I]. unfold acond_ok, b2_cNEC.
  cbn [ac_c ac_a ac_b].
  rewrite branch_ne_U, !U_SOff, U33, U35, !Z.add_0_r, !zcanon_id by (unfold M64; lia).
  apply negb_true_iff, Z.eqb_neq. exact HCL0. }
destruct (b2_seatA B ARx SK HYP fx E ly2 S2 Hp2 W2 regs2 regs0 mem2 md2 k pos c i vv ip Ex [b2_cLT; b2_cNE44; b2_cNEC]
  HPRE HB HAG H22 H23 Hc ltac:(lia) Hi3 Vq Ve HSP HEx HCS) as (HS & SHOK).
exw_run_to RUNTO HS HJ SHOK HPM B2_CX.
{ b2_awr U9 U19. }
exw_kept_of HFr (fun a => (exv_s1 E + 112 <= a < exv_s1 E + 144) \/ (e_q E <= a < e_q E + 8))
  ltac:(fun h => rewrite ?U9, ?U19 in h).
rename KEPT into K1.
lazymatch type of HS with st_ok _ ?Ex' _ _ =>
  assert (AG : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [e_x0 E + ip; nth (Z.to_nat ip) (e_x E) 0;
    e_x0 E + exv_len E; if c =? 123 then 125 else 93; Z.of_nat i; 56 * Z.of_nat i; 8 * Z.of_nat i])) Ex')
    by b2_agree HEx end.
assert (KR : forall r, In r b2_keep -> getr (ms_regs ms) r = getr regs2 r)
  by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs2 _ b2_keep HS AG ltac:(vm_compute; reflexivity) r Hr)).
prreg HS (24%bv : bv 5) RS8. cbn [ew ewset Nat.eqb] in RS8. rewrite E18 in RS8.
assert (HBE := b2_exb_end fx E ly2 S2 Hp2 W2 regs2 (ms_regs ms) mem2 md2 (ms_mem ms) _ k pos HPRE HBs HJ K1
  (fun a Ha => apresent_grows _ _ _ a HG Ha) HPM KR RS8).
pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 0 8 (SOff 32 0) (e_x0 E + ip) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(b2_in)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
destruct (KCUR (ms_mem ms) K1) as (Ve' & Vdep' & Vscr' & Vdl').
pmkst HS. b2_pc 0xa7c.
apply (HCX E ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) _ k pos (-1) Hn HPRE HBE).
- rewrite (KR 21%bv ltac:(b2_in)). exact H21.
- exists ip, (e_dep E + 1), dlc. split; [exact (conj VQ (conj Ve' (conj Vdep' (conj Vscr' Vdl'))))|].
  split; [exact Hdl|]. rewrite HVx. split; [reflexivity|]. split; lia.
Qed.
End p.
