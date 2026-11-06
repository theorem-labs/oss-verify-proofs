(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): SEGMENT L4j of
   the walk of LLVMFuzzerTestOneInput (B' 0x816cc). Proves seg_L4j_stmt of the B' cut file lib/AU/Ent102CutsB.v
   (read at blob a74a7497b9d0, commit b1ed4e6c944d): from cut_crs0
   (+0x2f4 = 0x819c0) the one `j` (`jal x0,-304`) to cut_exit (+0x1c4 = 0x81890). The jump changes no state; what
   moves is the room position's index, from e_i0 + |cno ++ pn ++ sc ++ rej| to e_i0 + |call_evs trp|, and the two
   are the same prefix of the run on the arm cut_crs0 carries (the refused reading, no reading run out): l4j_index.
   ec_inv is rebuilt from its parts BY NAME (CallB's ec_inv_pre) or BY TYPE (ec_conj_split), never by position.
   THE WILD BUDGET: ec_inv's journal is `exists WS, ajournal_xw .. WS /\ wbudget [] wk WS` with
   wk = ec_wk_crs0 (10) at cut_crs0 and ec_wk_exit (76) at cut_exit. The `j` is a no-call segment: the cut file's
   shared step ec_inv_wk_grow gives the materialized journal at a budget widened from 10 to 76 (the <= by vm_compute).
   First PORTED by port/a2b.py (sha256 f5113cbc90e503da) from lib/A/Prog/Ent102L4jA.v (seg_L4j_A, de3b748997f, on
   3b0db38483cf); re-proved on the exact-position record.
   - LISTING: lib/B/Listing_prog.v c97cc46b3e13 (B' d663f82d) with the PAListing PL_102_B of lib/B/Ent102PLB.v
     e0348e1212c9; generic over {PA : PAImg B_prog_listing} (route (b)). Shared helpers: lib/AU/Prog/Ent102CallB.v
     1c7a402519bc (ec_inv_pre, ec_conj_split / ec_conj_pick) and lib/AU/Ent102PosB.v 853ec706aac5 (ec_hruns_snoc,
     ec_call_evs_ranout_false), both taken by path; lib/Reusable/YCbqGwild.v aa0b10a819fa.
   - THE ONE SLOT READ: slot 189 (byte offset 756 = +0x2f4) is PW 0xed1ff06f on B' as on A' (the jump is
     pc-relative and both bodies are pc-relative-identical); a2b listed 0xed1ff06f as untranslated, and the B'
     listing confirms it unchanged (l4j_slot is checked by vm_compute on PL_102_B).
   rule 24: proves function LLVMFuzzerTestOneInput (reuse search: a Theorem Labs lane record, the internal file idx-llvm-newpin.txt
   exit=0, NEW walk on the #102 pins; CONFIRM `proof-index seg_L4j_B` 0 named, 0 on live heads), segment L4j.
   NUMERALS: 756 = 4 * 189 is a LENGTH (the slot's byte offset); -304 the jump's immediate. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog Ent102PLB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Ent102PosB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetReqAt PresetRun PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Import Ent102CallB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma l4j_slot : plookup (@pl_tpi _ PL_102_B) 756 = Some (PW 0xed1ff06f).
Proof. vm_compute. reflexivity. Qed.

Lemma l4j_decode : decode_any (Z_to_bv 32 0xed1ff06f) = Some (Jal 0 (Z_to_bv 21 (-304)), 4%Z).
Proof. vm_refl_bv. Qed.

Lemma l4j_imm : bv_signed (Z_to_bv 21 (-304)) = -304.
Proof. vm_compute. reflexivity. Qed.

Section L4j. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc B_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variable ec_ccut : ecx -> nat -> Z.
Variable ec_lcut : ecx -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp B_prog_listing PA B).
#[local] Notation ECX := (@ecx rc B_prog_listing PA).
#[local] Notation ECPRE := (@ec_pre fx rc ci cp PI RL B_prog_listing PA B EC_RA EC_EMPTY EC_SIO).

Lemma l4j_fetch : fetch_word SEGS (Z_to_bv 64 (BASE + 756)) = Some (Z_to_bv 32 0xed1ff06f).
Proof.
pose proof l4j_slot as Hpl. rewrite <- (@pl_tpi_eq _ PL_102_B) in Hpl.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma B_prog_listing pa_cert _ _ Hpl) as (Hck & _ & _).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (BASE + 756)) as [wz|] eqn:Hl; [|discriminate Hck].
apply Z.eqb_eq in Hck. subst wz.
exact (pa_fetch_ok _ _ Hl).
Qed.

(* THE INDEX. cut_crs0 is at e_i0 + |cno ++ pn ++ sc ++ rej| and cut_exit at e_i0 + |call_evs trp|, over the same
   grants e_os ++ [trp] (Ent102PosB.ec_hruns_snoc). On the refused arm with no reading run out they are the same
   prefix of the run: when n <= MAXB, call_evs = cno ++ call_rest (Ent102PosB.ec_call_evs_ranout_false) and
   call_rest = pn ++ sc ++ call_tail with call_tail = the starved reading = rej on a refused reading
   (PresetRun.v:352-363); when n > MAXB, call_evs = [] and both prefixes are the earlier calls' events (ec_pre's
   e_i0 = |hruns e_os|). *)
Lemma l4j_index : forall (E : ECX) trp,
  e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)) ->
  ec_ranout E trp = false ->
  fst (PjGrammar.jr_run (e_sm E) (e_x E) []) = None ->
  firstn (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rej E))%nat
    (PresetRun.hruns (e_sm E) (e_x E) (e_os E ++ [trp])) =
  firstn (e_i0 E + length (ec_call_evs E trp))%nat (PresetRun.hruns (e_sm E) (e_x E) (e_os E ++ [trp])).
Proof.
intros E trp Hi0 Hro Href.
assert (Hs : PresetRun.hruns (e_sm E) (e_x E) (e_os E ++ [trp]) =
  PresetRun.hruns (e_sm E) (e_x E) (e_os E) ++ ec_call_evs E trp).
{ destruct trp as [[o1 o2] o0]. exact (Ent102PosB.ec_hruns_snoc (e_sm E) (e_x E) (e_os E) o1 o2 o0). }
rewrite Hs.
destruct (Z_le_gt_dec (Z.of_nat (length (e_x E))) PresetReqAt.MAXB) as [Hn|Hn].
- (* the call runs: after check_no_overread, call_rest = pn ++ sc ++ the refused tail rej *)
  assert (Hr : PresetRun.call_rest (e_sm E) (e_x E) = ec_pn E ++ ec_sc E ++ ec_rej E).
  { unfold PresetRun.call_rest, PresetRun.call_tail. rewrite Href. reflexivity. }
  rewrite (Ent102PosB.ec_call_evs_ranout_false _ _ _ E trp Hn Hro), Hr. reflexivity.
- (* the size guard ends the call: no events *)
  assert (He : ec_call_evs E trp = []).
  { destruct trp as [[o1 o2] o0]. unfold ec_call_evs, PresetRun.call_evs. cbv zeta.
    rewrite (proj2 (Z.ltb_lt PresetReqAt.MAXB (Z.of_nat (length (e_x E)))) ltac:(lia)). reflexivity. }
  rewrite He, app_nil_r. cbn [length]. rewrite !firstn_all2 by lia. reflexivity.
Qed.

Lemma l4j_pos : forall (E : ECX) trp hist S, ECPRE E -> ec_ranout E trp = false ->
  fst (PjGrammar.jr_run (e_sm E) (e_x E) []) = None ->
  PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp])
    (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rej E))%nat (e_H0 E) hist S ->
  PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp]) (e_i0 E + length (ec_call_evs E trp))%nat
    (e_H0 E) hist S.
Proof.
intros E trp hist S Hpre Hro Href H.
(* ec_pre's index tie, BY ITS TYPE *)
assert (Hi0 : e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)))
  by (unfold ec_pre in Hpre; ec_conj_pick Hpre).
unfold PresetRoomPos.iface_room_pos in *. rewrite <- (l4j_index E trp Hi0 Hro Href). exact H.
Qed.

Theorem seg_L4j_B :
  @seg_L4j_stmt fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L4j_stmt, ec_laneR.
intros E fk HYP W c Hcut.
(* a no-call lane: the world does not move, so the plain SRr proof lifts to SRr' (YA0nH.SRr_SRr'); both cuts carry
   their journal at wle' (cut_crs0, cut_exitR WLE') *)
apply (SRr_SRr' SEGS (@YGcfRehidePost.RZ_cf rc)).
assert (HCOK : ec_ccut_ok ec_ccut) by (eapply ech_ccut_ok; exact HYP).
assert (HLOK : ec_lcut_ok ec_lcut) by (eapply ech_lcut_ok; exact HYP).
destruct Hcut as (ly & S & Hp & regs & mem & md & own & peak & cnt & k & trp & Hat & Hinv & HHp & Hro &
  HCC & HLC & Hrkd & Hfrm & HnMax & Href).
destruct Hat as (fy & Hfrm0 & Hkept & Hc). subst c.
assert (LAWS : AR_laws_x SEGS B ARc cf_head) by exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)).
assert (Htgt : btgt (Z_to_bv 64 (BASE + 756)) (bv_signed (Z_to_bv 21 (-304))) = w64 (@EC_EXIT rc B_prog_listing PA)).
{ rewrite l4j_imm, YCbn.btgt_lit. unfold w64, EC_EXIT, EC_BASE. f_equal. lia. }
unfold cfg_at.
change (w64 (@EC_AR_CRS0 rc B_prog_listing PA)) with (Z_to_bv 64 (BASE + 756)).
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  exact (step_jal_x0 SEGS regs _ _ _ _ _ l4j_fetch eq_refl l4j_decode).
- intros md' Hsame. rewrite (same_but_materialized_wvb md md' Hsame).
  cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Htgt.
  apply SRr_ret.
  exists ly, S, Hp, regs, mem, (with_vm_backing (m_vm_lazy md) (m_vm_materialized md') md), own, peak, cnt, 0, k,
    trp.
  split; [exists fy; split; [exact Hfrm0|]; split; [exact Hkept | reflexivity]|].
  split.
  { (* ec_inv at the new index and budget. Its parts BY NAME or TYPE: ec_pre by Ent102CallB's projection
       ec_inv_pre, the room position by ec_conj_pick (CallB has no projection for it); the position is moved by
       l4j_pos, the budgeted journal by the cut file's no-call step ec_inv_wk_grow, every other part
       (the ledger's `exists most own`, ...) is the cut's own *)
    assert (HPRE : ECPRE E) by (clear - Hinv; unfold ec_invR in Hinv; ec_conj_pick Hinv).
    assert (HPOS : exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp])
      (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rej E))%nat (e_H0 E) hist S)
      by (unfold ec_invR in Hinv; ec_conj_pick Hinv).
    assert (HPOS' : exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp])
      (e_i0 E + length (ec_call_evs E trp))%nat (e_H0 E) hist S).
    { destruct HPOS as (hist & Hh). exists hist. exact (l4j_pos E trp hist S HPRE Hro Href Hh). }
    unfold ec_invR in Hinv |- *. ec_conj_split Hinv.
    repeat lazymatch goal with |- _ /\ _ => split end.
    all: first
      [ assumption
      | lazymatch goal with
        | Hj : exists WS, _ /\ YCbqGwild.wbudget [] _ WS |- exists WS, _ /\ YCbqGwild.wbudget [] _ WS =>
          let HJ := fresh "HJ" in let Hb := fresh "Hb" in
          destruct Hj as (? & HJ & Hb);
          eapply ec_inv_wk_growR; [exact LAWS | exact HJ | exact Hb | apply Nat.leb_le; vm_compute; reflexivity]
        end ]. }
  split; [exact HHp|].
  split; [pose proof (proj2 (HCOK E 5%nat 11%nat) ltac:(lia)); lia|].
  split; [pose proof (proj2 (HLOK E 5%nat 11%nat) ltac:(lia)); lia|].
  split; [exact (proj1 Hrkd) | exact Hfrm].
Qed.

End L4j.

Print Assumptions seg_L4j_B.
About seg_L4j_B.
