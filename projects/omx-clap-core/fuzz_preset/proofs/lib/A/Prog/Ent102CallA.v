(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102CallA.v, with its module paths changed; 150 of its 347 lines of code are new or changed and 18 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, PIN sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): the SHARED CALL-SITE LEMMAS of the walk of
   LLVMFuzzerTestOneInput (entry 0x815e0), for every lane that calls a kit check_* text (L1 / L3 / L4 / L5b / L5c) or
   branches on a listing slot. Written on a Theorem Labs lane's decision (15:25Z, item (3)): ONE shared file, generic in the image
   ({PA : PAImg A_prog_listing}, the PAListing PL_102_A), no lib/A/PAImg_prog.v and no PresetCfnA / PresetCfnB import.
   No function is proved here.
   (a) THE CONTEXT OF A CALL: ec_chain_at builds the frame chain a callee's afn_pre_x takes at a call site of this body
       (s0 = sp0, the entry's ra and s0 saved at sp0 - 8 / sp0 - 16), with its spine [] or [ra0]; ec_ctx_call /
       ec_ctx_call_img give the kit's `prh_ctx ec_ctx0 G (r :: spine ch)` from ei_fp / ei_rets (prh_reach_top at [EC_RA],
       then prh_reach_call at the return site r).
   (b) THE PAYLOAD AT A CUT: ec_src_home gives src_rd and prhReader_home's block arm of a live allocator block that is
       an entry block (not a hidden head: the ledger's heads are the harness blocks, which ec_inv's Permutation
       separates from the entry's blocks); ec_src_home_cut is its corollary from a cut's ec_inv at 0 < e_n E.
       ec_src_home_cut reads ec_inv and ec_pre BY NAME, through the projections ec_inv_arcf / ec_inv_ledger /
       ec_inv_pre / ec_inv_pay / ec_inv_perm / ec_inv_bytes and ec_pre_payload / ec_pre_len / ec_pre_bytes /
       ec_pre_pay8 below, each proved by ec_conj_pick: it splits the definition's top-level conjunctions and picks
       the conjunct by its TYPE, so a conjunct added to or moved inside ec_pre / ec_inv breaks no proof here (the
       exact-position cuts added one to ec_pre and shifted the old positional pattern onto memnorm /\ pay8). A new
       BINDER of ec_inv changes only the projections' statements; their consumers take E .. i_c implicitly.
   (c) THE BRANCH STEP: ec_step_branch, a conditional branch slot of the listing at a generic image, taken or not
       (Ent102L6AfLem.v l6f_step_addi's form over Branch c, YK11.v step_branch_tk_gen / step_branch_ft_gen).
   (d) THE LEDGER'S TWO HARNESS CELLS (the decff kit, prh_ledger .. most own): ec_ledger_cells sets them to the values
       read there (prh_glob holds prh_most / prh_own as its own conjuncts, so the swap needs no val_mem determinism).
       A row after cut_cno calls a kit text that takes `prh_ledger .. most 0` from ec_inv's `exists most own,
       prh_ledger ..` and the cut's ec_most / ec_own_is; ONE copy for every row (a Theorem Labs lane's decision 18:43Z; first
       written in a Theorem Labs lane's lib/A/Prog/Ent102TailA.v).
   STATEMENT read: lib/A/Ent102CutsA.v (read at blob 00eff43e6ffa, commit aff1e4878ed5, the exact-position
   statements: ec_inv with the cut's index pair os_c i_c, ec_pre, ec_img's ei_fp / ei_rets, ec_ctx0,
   ec_call_rets, e_x / e_n / e_p).
   TAKEN BY PATH: lib/A/Prog/Ent102L6AfLem.v blob a37e0dc13d12 (a working branch: l6f_pc4,
   l6f_rdword_of_rd64, l6f_nodup_pw, l6f_nodup_app_l, l6f_garr8_kept); lib/A/Prog/S1Ledger.v (prh_ledger_hblock,
   prh_ablocks_nonneg_cf); the chain's two cases are Ent102L6Af.v's inline proof (a working branch :203-219).
   rule 24: proves function LLVMFuzzerTestOneInput (support lemmas of its segments; reuse search: proof-index
   LLVMFuzzerTestOneInput check_round_trip check_reject_clean_starved exit=0 + 364 cold refs, checker CONFIRM; NEW walk
   on the #102 pins).
   NUMERALS: 16 / 8 / 4 are LENGTHs (the frame record's two words, the word, an instruction); 4096 is the engine's low
   page; 2 ^ 40 / 2 ^ 64 are the code-span and word ranges; 2 ^ 26 is ec_pre's payload bound. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0scf YG0sshcf YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Ent102L6AfLem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Pure facts. *)

(* two distinct members of a list whose images are pairwise R are related one way or the other *)
Lemma ec_pw_mem : forall (g : Z * Z -> Z * Z) (R : Z * Z -> Z * Z -> Prop) (l : list (Z * Z)) x y,
  YG0f.pairwise R (map g l) -> In x l -> In y l -> x <> y -> R (g x) (g y) \/ R (g y) (g x).
Proof.
intros g R l. induction l as [|z r IH]; intros x y HP Hx Hy Hne; [destruct Hx|].
cbn [map YG0f.pairwise] in HP. destruct HP as [Hf Hr]. rewrite Forall_forall in Hf.
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- exfalso. exact (Hne eq_refl).
- left. apply Hf. apply in_map. exact Hy.
- right. apply Hf. apply in_map. exact Hx.
- exact (IH x y Hr Hx Hy Hne).
Qed.

(* a base outside the head list is skipped by nothing *)
Section HS. Context {cp : CfParams}.
Lemma ec_hd_skip_out : forall (Hp : list Z) p, ~ In p Hp -> hd_skip Hp p = 0.
Proof.
intros Hp p Hn. unfold hd_skip.
destruct (existsb (Z.eqb p) Hp) eqn:E; [|reflexivity].
apply existsb_exists in E as (q & Hq & Eq). apply Z.eqb_eq in Eq. subst q. contradiction.
Qed.
End HS.

(* ---------------------------------------------------------------------- *)
(* 2. (a) The frame chain at a call site of this body: the record at sp0 (ra0 at sp0 - 8, s0 at sp0 - 16), or none
      when sp0 is within 16 bytes of the stack top (achain's left disjunct). Ent102L6Af.v :203-219's two cases. *)
Section CH. Context {rc : YM05.RunCeil}.
Lemma ec_chain_at : forall ly (rd : reader) sp sp0 ra0 s00,
  rd64 rd (sp0 - 8) ra0 -> rd64 rd (sp0 - 16) s00 -> 0 <= ra0 < 2 ^ 64 -> 0 <= s00 < 2 ^ 64 ->
  s00 < alloc_ceiling -> 4096 <= ra0 -> alloc_ceiling <= sp0 -> sp0 mod 8 = 0 -> ly_top ly <= 2 ^ 64 ->
  sp + 16 <= sp0 ->
  exists ch, achain ly rd sp sp0 ch /\ (spine ch = [] \/ spine ch = [ra0]).
Proof.
intros ly rd sp sp0 ra0 s00 Hra Hs0 Hr Hs Hs0c Hra4 Hceil Hal Htop Hsp.
destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt|Hge].
- exists [(sp0, ra0, s00)]. split; [|right; reflexivity].
  apply (achain_push ly rd rd sp0 s00 ra0 [] sp).
  + apply achain_low. exact Hs0c.
  + exact Htop.
  + intros a _. reflexivity.
  + apply l6f_rdword_of_rd64; [exact Hra | exact Hr].
  + apply l6f_rdword_of_rd64; [exact Hs0 | exact Hs].
  + exact Hra4.
  + exact Hceil.
  + exact Hal.
  + exact Hlt.
  + exact Hsp.
- exists []. split; [|left; reflexivity]. left. split; [right; left; lia | reflexivity].
Qed.
End CH.

(* (a) the kit's call-site context: this body keeps a frame pointer (ei_fp) and r is a return site of its call to G
   (ei_rets), so G runs in r :: [EC_RA], whose prefixes are the contexts a cut chain observes *)
Section CTX. Context {PI : PrhImg}.
Variable EC_RA : Z.
Lemma ec_ctx_call : forall (G : prh_fn) (r : Z) (ch : list (Z * Z * Z)),
  @pi_fp PI F_LLVMFuzzerTestOneInput = true -> In r (@pi_call_rets PI F_LLVMFuzzerTestOneInput G) ->
  spine ch = [] \/ spine ch = [EC_RA] ->
  prh_ctx (ec_ctx0 EC_RA) G (r :: spine ch).
Proof.
intros G r ch Hfp Hr Hsp. unfold ec_ctx0.
pose proof (prh_reach_call [[EC_RA]] F_LLVMFuzzerTestOneInput G [EC_RA] r
  (prh_reach_top [[EC_RA]] [EC_RA] (or_introl eq_refl)) Hr) as H.
rewrite Hfp in H.
exists [r; EC_RA], (length (r :: spine ch)). split; [exact H|].
destruct Hsp as [-> | ->]; reflexivity.
Qed.
End CTX.

(* (d) the ledger with its two harness cells set to the values read there *)
Section LC. Context {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg} {PA : @PAImg rc A_prog_listing}.
Lemma ec_ledger_cells : forall B ly S Hp W mem Lam peak cnt fail ran most own most' own',
  @prh_ledger rc cp PI A_prog_listing PA B ly S Hp W mem Lam peak cnt fail ran most own ->
  @prh_most rc PI A_prog_listing PA W mem most' -> @prh_own rc PI A_prog_listing PA W mem own' ->
  @prh_ledger rc cp PI A_prog_listing PA B ly S Hp W mem Lam peak cnt fail ran most' own'.
Proof.
intros B ly S Hp W mem Lam peak cnt fail ran most own most' own' (HG & H1) Hm Ho.
destruct HG as (G1 & G2 & G3 & G4 & G5 & _ & _ & G8).
split; [|exact H1].
exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj Hm (conj Ho G8))))))).
Qed.
End LC.

(* the top-level conjuncts of a hypothesis (a syntactic `_ /\ _` only: a conjunct that is itself a Definition, e.g.
   ajournal_x or ec_pre inside ec_inv, stays one hypothesis until it is unfolded), then the goal BY ITS TYPE *)
Ltac ec_conj_split H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "Ec" in let H2 := fresh "Ec" in destruct H as [H1 H2]; ec_conj_split H1; ec_conj_split H2
  | _ => idtac
  end.
Ltac ec_conj_pick H := ec_conj_split H; assumption.

(* ---------------------------------------------------------------------- *)
(* 3. The image-generic part: the context from ec_img, the payload at a cut, the branch step. *)
Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.

#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Notation SIGMA := (@pa_sigma rc A_prog_listing PA).
#[local] Notation ECX := (@ecx rc A_prog_listing PA).
#[local] Notation ECPRE := (@ec_pre fx rc ci cp PI RL A_prog_listing PA B EC_RA EC_EMPTY EC_SIO).
#[local] Notation ECINV := (@ec_inv fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO).

(* ---- ec_pre's parts BY NAME (type-directed; ec_conj_pick above) ---- *)
Lemma ec_pre_payload : forall {E : ECX}, ECPRE E ->
  (e_n E = 0 /\ e_p E = EC_EMPTY) \/ (0 < e_n E < 2 ^ 26 /\ In (e_p E, e_n E) (ablocks B (e_ly E) (e_S E))).
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma ec_pre_len : forall {E : ECX}, ECPRE E -> e_n E = Z.of_nat (length (e_pl E)).
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma ec_pre_bytes : forall {E : ECX}, ECPRE E -> garr8 SEGS (mrestrict (w_H (e_W E)) (e_mem E)) (e_p E) (e_x E).
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma ec_pre_pay8 : forall {E : ECX}, ECPRE E -> 0 < e_n E -> e_p E + e_n E + 8 <= YM05.alloc_ceiling.
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.

(* ---- ec_inv's parts BY NAME; E .. i_c implicit, so a consumer's call does not depend on ec_inv's arity ---- *)
Lemma ec_inv_arcf : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> ARcf SEGS B ly S Hp W mem md.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H.
unfold ec_inv in H. destruct H as [(WS & HJ & _) _].
unfold ajournal_xw, ajournal_xb, ajournal_xbR, ec_ARx in HJ. cbv beta in HJ. ec_conj_pick HJ.
Qed.
Lemma ec_inv_ledger : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  exists most own, prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAX ran most own.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. ec_conj_pick H. Qed.
Lemma ec_inv_pre : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> ECPRE E.
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. ec_conj_pick H. Qed.
Lemma ec_inv_pay : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> e_n E = 0 \/ In (e_p E, e_n E) (ablocks B ly S).
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. ec_conj_pick H. Qed.
Lemma ec_inv_perm : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  Permutation (ablocks B ly S) (ck_hblks Lam ++ ablocks B (e_ly E) (e_S E)).
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. ec_conj_pick H. Qed.
Lemma ec_inv_bytes : forall {E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  forall i, 0 <= i < e_n E -> aview SEGS (w_H W) mem (e_p E + i) = aview SEGS (w_H (e_W E)) (e_mem E) (e_p E + i).
Proof. intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_inv in H. ec_conj_pick H. Qed.


(* (a) at one of the body's 19 call sites (ec_call_rets), from ec_img's ei_fp / ei_rets *)
Lemma ec_ctx_call_img : forall (G : prh_fn) (r : Z) (ch : list (Z * Z * Z)),
  ec_img (L := A_prog_listing) (PA := PA) B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ->
  In (G, r) (ec_call_rets (L := A_prog_listing) (PA := PA)) ->
  spine ch = [] \/ spine ch = [EC_RA] ->
  prh_ctx (ec_ctx0 EC_RA) G (r :: spine ch).
Proof.
intros G r ch HI Hin Hsp.
apply (ec_ctx_call EC_RA G r ch); [| | exact Hsp].
- eapply ei_fp. exact HI.
- eapply ei_rets; [exact HI | exact Hin].
Qed.

(* (b) THE PAYLOAD: a live allocator block (p, n) of the current state that is also an entry block, at a state whose
   blocks are the harness blocks ck_hblks Lam plus the entry's, read by a check_* text as its source. It is not a
   hidden head (every head base is a harness block's, and the Permutation keeps harness and entry blocks apart), so
   ARcf's shadow law gives its whole range addressable, and its bytes are the text's src_rd. *)
Lemma ec_src_home : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran ly0 S0 p n (x : list Z),
  ARcf SEGS B ly S Hp W mem md ->
  (exists most own, prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own) ->
  Permutation (ablocks B ly S) (ck_hblks Lam ++ ablocks B ly0 S0) ->
  In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly S) ->
  n = Z.of_nat (length x) -> 0 < n -> p + n + 8 <= YM05.alloc_ceiling ->
  garr8 SEGS (mrestrict (w_H W) mem) p x ->
  src_rd W mem p x /\ prhReader_home B ly S Hp Lam p n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran ly0 S0 p n x HAR (most & own & HLED) HPERM Hin0 Hin Hn Hn0 H8 Hg.
pose proof (AR_blocks_law_ok_cf SEGS B ly S Hp W mem md p n HAR Hin) as (B16 & B4096 & BC & BA & _ & Hpw & BN).
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (HNH : ~ In p Hp).
{ intros Hh.
  pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HH.
  apply (Permutation_in _ HH) in Hh. apply in_map_iff in Hh as ((a & k) & Ea & HinL). cbn [fst] in Ea.
  pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLED HinL) as (Hk0 & Hb & _).
  rewrite Ea in Hb.
  assert (HND : List.NoDup (ablocks B ly S))
    by exact (l6f_nodup_pw _ (prh_ablocks_nonneg_cf B ly S Hp W mem md HAR) Hpw).
  assert (Hne : (p, k + cf_head) <> (p, n)).
  { intros E1. pose proof (Permutation_NoDup HPERM HND) as HND2.
    assert (Hi1 : In (p, n) (ck_hblks Lam)).
    { rewrite <- E1. unfold ck_hblks. rewrite <- Ea.
      exact (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Lam (a, k) HinL). }
    exact (l6f_nodup_app_l _ _ _ HND2 Hi1 Hin0). }
  pose proof cf_head_nonneg as C0.
  destruct (ec_pw_mem (fun b : Z * Z => (fst b, req_size (snd b))) zdisjoint (ablocks B ly S) _ _ Hpw Hb Hin Hne)
    as [Hd | Hd]; unfold zdisjoint in Hd; cbn [fst snd] in Hd;
    unfold req_size in Hd; destruct (Z.eqb_spec (k + cf_head) 0); destruct (Z.eqb_spec n 0); lia. }
pose proof (AR_shadow_law_ok_cf SEGS B ly S Hp W mem md p n HAR Hin) as (BS & HV).
rewrite (ec_hd_skip_out Hp p HNH), Z.add_0_r, Z.sub_0_r, Hrq in BS. rewrite Hrq in HV, BA, BC.
pose proof ASAN_CEIL_range as AC.
split.
- unfold src_rd. rewrite <- Hn.
  split; [exact Hg|]. split; [exact B4096|]. split; [lia|].
  split.
  { unfold amem_range. unfold in_app in BA. destruct BA as [_ [BL | [BH1 BH2]]].
    - left. unfold kLowMemEnd, kLowShadowBeg in *. lia.
    - right. unfold ASAN_CEIL in AC. unfold kHighMemEnd, kHighMemBeg in *. lia. }
  split.
  { eapply block_shadow_range; [exact BS | lia | lia]. }
  intros _. exact HV.
- right. exists p, n. split; [exact Hin|]. split; [exact HNH|]. lia.
Qed.

(* (b) at a cut: ec_inv gives the payload block at the entry (ec_pre) and now, its bytes (ec_pre's garr8 and the
   kept clause), the ledger and the Permutation, and ec_pre the + 8; every part is taken by name *)
Lemma ec_src_home_cut : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk,
  ECINV E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  0 < e_n E ->
  src_rd W mem (e_p E) (e_x E) /\ prhReader_home B ly S Hp Lam (e_p E) (e_n E).
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk Hinv Hn0.
pose proof (ec_inv_pre Hinv) as HPRE.
destruct (ec_pre_payload HPRE) as [(Hz & _) | (_ & Hin0)]; [lia|].
destruct (ec_inv_pay Hinv) as [Hz | Hin]; [lia|].
assert (HLx : e_n E = Z.of_nat (length (e_x E)))
  by (unfold e_x, ec_bytes; rewrite length_map; exact (ec_pre_len HPRE)).
apply (ec_src_home ly S Hp W mem md Lam peak cnt SIZE_MAX ran (e_ly E) (e_S E) (e_p E) (e_n E) (e_x E)
  (ec_inv_arcf Hinv) (ec_inv_ledger Hinv) (ec_inv_perm Hinv) Hin0 Hin HLx Hn0 (ec_pre_pay8 HPRE Hn0)).
apply (l6f_garr8_kept (w_H (e_W E)) (w_H W) (e_mem E) mem); [|exact (ec_pre_bytes HPRE)].
intros i Hi. rewrite <- HLx in Hi. exact (ec_inv_bytes Hinv i Hi).
Qed.

(* (c) THE BRANCH STEP at a generic image: the slot at offset k is `b<c> rs1, rs2, imm` with target offset
   tgt = k + imm; the continuation is asked at the target when the branch is taken and at k + 4 when not *)
Lemma ec_step_branch : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w tgt : Z) (c : branch_cond) (rs1 rs2 : bv 5) (imm : bv 13),
  0 <= k < 2 ^ 40 -> 0 <= tgt < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_A) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch c rs1 rs2 imm, 4%Z) ->
  k + bv_signed imm = tgt ->
  (branch_taken c (getr regs rs1) (getr regs rs2) = true -> forall X,
     SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + tgt)) mem (YK11.seg_rom SEGS))
       (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  (branch_taken c (getr regs rs1) (getr regs rs2) = false -> forall X,
     SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
       (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w tgt c rs1 rs2 imm Hk Ht Hpl Hd Etg HT HF.
pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
pose proof (pa_fetch_pw (PL := PL_102_A) (PI := PA) k w Hpl) as Hf.
destruct (branch_taken c (getr regs rs1) (getr regs rs2)) eqn:Hc.
- eapply (SRr_step SEGS (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
  + rewrite (restrict_mkst_fx (fx := fx)).
    exact (step_branch_tk_gen (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS) (Z_to_bv 32 w) c rs1 rs2 imm Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
  + intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
    cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
    replace (btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm)) with (Z_to_bv 64 (BASE + tgt)).
    * apply HT. reflexivity.
    * unfold btgt, v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
- eapply (SRr_step SEGS (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
  + rewrite (restrict_mkst_fx (fx := fx)).
    exact (step_branch_ft_gen (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS) (Z_to_bv 32 w) c rs1 rs2 imm Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
  + intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
    cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
    rewrite (l6f_pc4 k Hk). apply HF. reflexivity.
Qed.

(* THE SAME PARTS OVER A WORLD RELATION Rel (the re-hiding move: the cuts after a free carry ec_invR at wle', the
   cut file's WLE'): the projections, the payload at a cut and the branch step over ec_invR / YA0nH.SRrG. ec_inv is
   ec_invR at wle (the cut file's ec_inv_R_wle, by reflexivity). *)
#[local] Notation ECINVR Rel := (@ec_invR fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO Rel).
Lemma ec_inv_arcfR : forall {Rel E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINVR Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> ARcf SEGS B ly S Hp W mem md.
Proof.
intros Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H.
unfold ec_invR in H. destruct H as [(WS & HJ & _) _].
unfold ajournal_xwR, ajournal_xbR, ec_ARx in HJ. cbv beta in HJ. ec_conj_pick HJ.
Qed.
Lemma ec_inv_ledgerR : forall {Rel E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINVR Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  exists most own, prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAX ran most own.
Proof. intros Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. ec_conj_pick H. Qed.
Lemma ec_inv_preR : forall {Rel E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINVR Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> ECPRE E.
Proof. intros Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. ec_conj_pick H. Qed.
Lemma ec_inv_payR : forall {Rel E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINVR Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk -> e_n E = 0 \/ In (e_p E, e_n E) (ablocks B ly S).
Proof. intros Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. ec_conj_pick H. Qed.
Lemma ec_inv_permR : forall {Rel E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINVR Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  Permutation (ablocks B ly S) (ck_hblks Lam ++ ablocks B (e_ly E) (e_S E)).
Proof. intros Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. ec_conj_pick H. Qed.
Lemma ec_inv_bytesR : forall {Rel E fk ly S Hp} {W : world SEGS} {mem md own Lam peak cnt ran k os_c i_c wk},
  ECINVR Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  forall i, 0 <= i < e_n E -> aview SEGS (w_H W) mem (e_p E + i) = aview SEGS (w_H (e_W E)) (e_mem E) (e_p E + i).
Proof. intros Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H. unfold ec_invR in H. ec_conj_pick H. Qed.
Lemma ec_src_home_cutR : forall Rel (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k os_c i_c wk,
  ECINVR Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  0 < e_n E ->
  src_rd W mem (e_p E) (e_x E) /\ prhReader_home B ly S Hp Lam (e_p E) (e_n E).
Proof.
intros Rel E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk Hinv Hn0.
pose proof (ec_inv_preR Hinv) as HPRE.
destruct (ec_pre_payload HPRE) as [(Hz & _) | (_ & Hin0)]; [lia|].
destruct (ec_inv_payR Hinv) as [Hz | Hin]; [lia|].
assert (HLx : e_n E = Z.of_nat (length (e_x E)))
  by (unfold e_x, ec_bytes; rewrite length_map; exact (ec_pre_len HPRE)).
apply (ec_src_home ly S Hp W mem md Lam peak cnt SIZE_MAX ran (e_ly E) (e_S E) (e_p E) (e_n E) (e_x E)
  (ec_inv_arcfR Hinv) (ec_inv_ledgerR Hinv) (ec_inv_permR Hinv) Hin0 Hin HLx Hn0 (ec_pre_pay8 HPRE Hn0)).
apply (l6f_garr8_kept (w_H (e_W E)) (w_H W) (e_mem E) mem); [|exact (ec_pre_bytes HPRE)].
intros i Hi. rewrite <- HLx in Hi. exact (ec_inv_bytesR Hinv i Hi).
Qed.
Lemma ec_step_branchR : forall (Rel : world SEGS -> world SEGS -> Prop) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w tgt : Z) (c : branch_cond) (rs1 rs2 : bv 5) (imm : bv 13),
  0 <= k < 2 ^ 40 -> 0 <= tgt < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_A) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch c rs1 rs2 imm, 4%Z) ->
  k + bv_signed imm = tgt ->
  (branch_taken c (getr regs rs1) (getr regs rs2) = true -> forall X,
     SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + tgt)) mem (YK11.seg_rom SEGS))
       (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  (branch_taken c (getr regs rs1) (getr regs rs2) = false -> forall X,
     SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
       (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros Rel W regs mem md Q k w tgt c rs1 rs2 imm Hk Ht Hpl Hd Etg HT HF.
pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
pose proof (pa_fetch_pw (PL := PL_102_A) (PI := PA) k w Hpl) as Hf.
destruct (branch_taken c (getr regs rs1) (getr regs rs2)) eqn:Hc.
- eapply (SRrG_step SEGS Rel (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
  + rewrite (restrict_mkst_fx (fx := fx)).
    exact (step_branch_tk_gen (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS) (Z_to_bv 32 w) c rs1 rs2 imm Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
  + intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
    cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
    replace (btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm)) with (Z_to_bv 64 (BASE + tgt)).
    * apply HT. reflexivity.
    * unfold btgt, v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
- eapply (SRrG_step SEGS Rel (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
  + rewrite (restrict_mkst_fx (fx := fx)).
    exact (step_branch_ft_gen (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS) (Z_to_bv 32 w) c rs1 rs2 imm Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
  + intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
    cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
    rewrite (l6f_pc4 k Hk). apply HF. reflexivity.
Qed.
End G.

Print Assumptions ec_chain_at.
Print Assumptions ec_ctx_call_img.
Print Assumptions ec_src_home_cut.
Print Assumptions ec_step_branch.
