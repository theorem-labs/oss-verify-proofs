(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry of descriptors_panel_get's walk (plugin-hostd/fuzz_command.asan) and the two arms of the inlined record(), from 0x8d10c to the join at 0x8d180, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment proved from the next one's statement) with the shared seed pieces of lib/A/Prog/RecBTemplate.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_panel_get_s7.v, with its module paths and module names changed; 2926 of its 3000 lines of code are new or changed and 823 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102: pin sha256 d663f82d7f488d30, unstripped twin
   c90d4fa54d43160b): the program walk of fuzz_preset.c's read_members (out of line on the #102 pins: B' 0x82554, 724
   bytes, 181 words; slot 930 of a Theorem Labs lane's whole-program listing lib/B/Listing_prog.v, v3 blob c97cc46b3e13, YPsym.v
   b6f5a85d234d) against the text tread_members_specX (lib/A/PRH_FnCheck.v blob 4cb899514e6c :805, every fuzz_preset/lib
   path of decff67d721f taken on base ed6e9a1a2e98).
   rule 24: proves function read_members (lookup: proof-index read_members, 2026-10-29T11:5xZ, exit 1: no released
   FUNCTION proof; checker R24ReadMembers CONFIRM). Verdict: none: written new.
   PARAMETRIC IN THE IMAGE INSTANCE: the walk is over {PA : PAImg B_prog_listing} with the listing's own tables
   (PL_rm_B below, the terms of PAImg_prog.v's instance) and the pure image facts of PA as named hypotheses rm_pa_...;
   lib/B/Prog/read_members_Bp.v instantiates it at PI_prog_B and the B' record, deciding those facts and RM_IMG by
   vm_compute there.
   HYPOTHESES (Section f):
   - LAWS : AR_laws_x (the allocator relation's engine laws) at hl = cf_head, TL : PALibCore (the shadow-base GOT word
     and cell).
   - PJ_GET / PJ_GET_STR: the tpj_get_specX / tpj_get_str_specX as they stand (PRH_FnPj.v blob a21e5a5cb897 :570, :587;
     the g_most / g_own cells are inside prh_ledger's most / own there, so no keep is added).
   - RM_IMG (ruled by a Theorem Labs lane at 14:5xZ; the kit owner at 14:44Z): a fact about the asyms record B at this image - the key literals
     and the table read_members.top are read-only image bytes, not runtime-owned, not errno, with their shadow - in the
     kept_img / ro_shadow_ok words; discharged at the #102 B' asyms instance by vm_compute, never a caller premise.
   - NO GAP PREMISE: the former RM_G3 is LAWS' own fields at hl = cf_head - field 14 (alx_hshadow, YCbqG.v) for the
     shadow of the nodes below the root, field 22 (alx_hhead, used through YCbqG's hhead_not_addressable_x) for the
     hidden head of the root's block.
   ENGINE: YCbqG 9c40f328a6d4 (the P'' base's, with field 22); a Theorem Labs lane s1b's memory-invariant runners by path
   from 459129c18903: lib/Reusable/YC80x.v 14f84f225e8f, YC1fPx.v 7814b594066f, YSRrMemnorm.v 5ffa8525936b. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnPj PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
(* the PLAIN build's sink head must never fill SK here (YC1fP.v:23-33 does the same): every SK below is explicit *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the listing's own tables (PAImg_prog.v 8bcc2c9e7809-listing instance :177-181, the same terms; Required from no
   file that needs IMG_TOP_B): the engine's vm_compute needs a closed table ---- *)
Definition B_prog_tpi_rm : ptree asym := ptree_of_list B_prog_listing.
Definition B_prog_tw_rm : ctable := Eval vm_compute in (tw_of 0 B_prog_listing).
Definition PL_rm_B : PAListing B_prog_listing :=
{| pl_tpi := B_prog_tpi_rm; pl_tpi_eq := eq_refl; pl_tw := B_prog_tw_rm; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.

(* read_members' place in the listing (DERIVED: B_prog_sigma AS_read_members = 0x82554 = B_prog_base + 4 * 930) *)
Definition RMB_SLOT : nat := 930.
Definition AF_rmB : Z := 4 * Z.of_nat RMB_SLOT.

(* ======== SHARED TEXT (byte for byte the same in lib/A/Prog/read_members.v; source of record
   a Theorem Labs lane's worker file rm-shared-texts.v) ======== *)
Section k0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
(* the key literals the function passes, (address, length) from the listing: (A_OBJ 2) + the PAddHi offset; the six
   keys of read_members.top are the first six (the table's pointers, an image fact of PA) *)
Definition rm_keys : list (Z * Z) :=
  map (fun on => (pa_val (A_OBJ 2) + fst on, snd on))
    [(0x11020, 6); (0x11040, 2); (0x11060, 4); (0x11080, 7); (0x110a0, 9); (0x110c0, 10); (0x110e0, 6);
     (0x11100, 5); (0x11120, 6); (0x11140, 6); (0x11160, 5); (0x11180, 8); (0x111a0, 5)].
End k0.

(* ======== this image's key table: (listing offset off (A_OBJ 2), the key's bytes) - the bytes are an image fact of PA
   (rm_pa_keys), the same keys and lengths as rm_keys (rm_keytab_keys) ======== *)
Definition rm_keytab : list (Z * list Z) :=
  [(0x11020, [102; 111; 114; 109; 97; 116]);                (* "format" *)
   (0x11040, [105; 100]);                                    (* "id" *)
   (0x11060, [110; 97; 109; 101]);                           (* "name" *)
   (0x11080, [99; 97; 114; 114; 105; 101; 115]);             (* "carries" *)
   (0x110a0, [99; 114; 101; 97; 116; 101; 100; 65; 116]);    (* "createdAt" *)
   (0x110c0, [109; 111; 100; 105; 102; 105; 101; 100; 65; 116]); (* "modifiedAt" *)
   (0x110e0, [112; 97; 114; 97; 109; 115]);                  (* "params" *)
   (0x11100, [115; 116; 97; 116; 101]);                      (* "state" *)
   (0x11120, [112; 108; 117; 103; 105; 110]);                (* "plugin" *)
   (0x11140, [115; 121; 109; 98; 111; 108]);                 (* "symbol" *)
   (0x11160, [118; 97; 108; 117; 101]);                      (* "value" *)
   (0x11180, [101; 110; 99; 111; 100; 105; 110; 103]);       (* "encoding" *)
   (0x111a0, [98; 121; 116; 101; 115])].                     (* "bytes" *)
(* the little-endian byte j of the 8-byte word v *)
Definition rm_byte (v : Z) (j : nat) : Z := Z.land (Z.shiftr v (8 * Z.of_nat j)) 255.

(* ======== image-free pieces, COPIED (not Required: their files are not on this base) from lib/A/Prog/S6PjCommon.v
   698e5bc027e5 (the gs_ lemmas) and lib/A/Prog/PRW_StepKit.v 0df3991c13f4 (the rest), renamed with the prefix rm_ ======== *)
Lemma rm_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
Lemma rm_mr_keep : forall E' rs (m m' : word -> option byte) a,
  frame_of E' rs m m' -> ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros E' rs m m' a HF Hn Ha. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.
Lemma rm_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma rm_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.
Lemma rm_denot_off : forall E n w c, ew E n = Z_to_bv 64 w -> sv_denot E (SOff n c) = Z_to_bv 64 (w + c).
Proof.
intros E n w c Hn. apply bv_eq. rewrite denot_SOff, Hn, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
Lemma rm_tagU : forall (E' : env) n v, ew E' n = Z_to_bv 64 (tag v) -> U E' (SExt true 32 (SOff n 0)) = tag v.
Proof.
intros E' n v H. rewrite U_SExt, (U_atom E' n (tag v) H) by (destruct v; cbn [tag]; lia).
destruct v; vm_compute; reflexivity.
Qed.
Lemma rm_items_in : forall (P : Z -> jv -> list (Z * Z) -> Prop) l a D b,
  pj_itemsR P a l D -> In b D -> exists i u D1, nth_error l i = Some u /\ P (a + 56 * Z.of_nat i) u D1 /\ In b D1.
Proof.
intros P l. induction l as [|u r IH]; intros a D b H Hb; cbn [pj_itemsR] in H; [subst D; destruct Hb|].
destruct H as (D1 & D2 & -> & H1 & H2). apply in_app_or in Hb as [Hb|Hb].
- exists 0%nat, u, D1. split; [reflexivity|]. split; [|exact Hb]. replace (a + 56 * Z.of_nat 0) with a by lia. exact H1.
- destruct (IH (a + 56) D2 b H2 Hb) as (i & u' & D1' & Hi & HP & Hin).
  exists (S i), u', D1'. split; [exact Hi|]. split; [|exact Hin].
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact HP.
Qed.
Section gc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation SEGS := (@pa_segs _ L PA).
Lemma rm_agree : forall (m m' : word -> option byte) (X : Z -> Prop),
  (forall x, X x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) -> pj_agreeR SEGS m m' X.
Proof.
intros m m' X H x Hx. unfold mbyte, writable_at. rewrite <- (H x Hx) at 1.
split; [reflexivity|]. unfold wview. rewrite (H x Hx). auto.
Qed.
Lemma rm_val8_uniq : forall (m : word -> option byte) a v v',
  val_mem SEGS m a 8 v -> val_mem SEGS m a 8 v' -> 0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
intros m a v v' H H' Hv Hv'.
assert (Bk : forall k, (k < 8)%nat -> YO0f.le_byte v 8 k = YO0f.le_byte v' 8 k).
{ intros k Hk. pose proof (H k Hk) as A. pose proof (H' k Hk) as A'. rewrite A in A'. injection A' as Eb.
  change (bv_unsigned (Z_to_bv 8 (YO0f.le_byte v 8 k)) = bv_unsigned (Z_to_bv 8 (YO0f.le_byte v' 8 k))) in Eb.
  rewrite !Z_to_bv_unsigned in Eb. unfold bv_wrap, bv_modulus in Eb.
  change (2 ^ Z.of_N 8) with 256 in Eb. unfold YO0f.le_byte in *. rewrite !Z.mod_mod in Eb by lia. exact Eb. }
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 64) as [Hl|Hl].
- pose proof (Z.div_pos i 8 Hi ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm.
  pose proof (Z.div_mod i 8 ltac:(lia)) as Hdm.
  assert (Hd8 : i / 8 < 8) by (apply Z.div_lt_upper_bound; lia).
  assert (Hk : (Z.to_nat (i / 8) < 8)%nat) by lia.
  pose proof (Bk _ Hk) as B0. unfold YO0f.le_byte in B0. rewrite Z2Nat.id in B0 by lia.
  replace (8 * Z.of_nat 8) with 64 in B0 by reflexivity. rewrite !(Z.mod_small _ (2 ^ 64)) in B0 by lia.
  assert (T : forall x, Z.testbit x i = Z.testbit (Z.shiftr x (8 * (i / 8)) mod 256) (i mod 8)).
  { intros x. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. f_equal. lia. }
  rewrite !T, B0. reflexivity.
- rewrite <- (Z.mod_small v (2 ^ 64)) by lia. rewrite <- (Z.mod_small v' (2 ^ 64)) by lia.
  rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma rm_node_hdr : forall m lblk p t D, pj_nodeR SEGS m lblk p t D ->
  exists num str kids keys n cap, pj_hdrR SEGS m p (tag t) num str kids keys n cap.
Proof.
intros m lblk p t D H. destruct t; cbn [pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & _); exists num, str, kids, keys, n, cap; exact Hh.
Qed.
Lemma rm_mems_in : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D b,
  pj_memsR SEGS m lblk P a ka l D -> In b D ->
  (exists x k nm, b = (x, k) /\ pj_cstrR SEGS m lblk x k nm) \/
  exists i nm u D1, nth_error l i = Some (nm, u) /\ P (a + 56 * Z.of_nat i) u D1 /\ In b D1.
Proof.
intros m lblk P l. induction l as [|[nm u] r IH]; intros a ka D b H Hb; cbn [pj_memsR] in H; [subst D; destruct Hb|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2).
destruct Hb as [<- | Hb]; [left; exists x, k, nm; split; [reflexivity | exact Hc]|].
apply in_app_or in Hb as [Hb|Hb].
- right. exists 0%nat, nm, u, D1. split; [reflexivity|]. split; [|exact Hb].
  replace (a + 56 * Z.of_nat 0) with a by lia. exact H1.
- destruct (IH (a + 56) (ka + 8) D2 b H2 Hb) as [L' | (i & nm' & u' & D1' & Hi & HP & Hin)]; [left; exact L'|].
  right. exists (S i), nm', u', D1'. split; [exact Hi|]. split; [|exact Hin].
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact HP.
Qed.
Lemma rm_nodeR_lblk : forall t m lblk p D, pj_nodeR SEGS m lblk p t D -> forall b, In b D -> lblk (fst b) (snd b).
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros m lblk p D H b Hb; cbn [pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb2).
- destruct Hb2 as (_ & _ & _ & _ & _ & ->). destruct Hb.
- destruct Hb2 as (_ & _ & _ & _ & _ & ->). destruct Hb.
- destruct Hb2 as (_ & _ & _ & _ & _ & ->). destruct Hb.
- destruct Hb2 as (_ & _ & _ & _ & _ & k & Hc & ->). destruct Hb as [<- | []]. exact (proj1 Hc).
- destruct Hb2 as (_ & _ & _ & _ & k & Hc & ->). destruct Hb as [<- | []]. exact (proj1 Hc).
- destruct Hb2 as (_ & _ & _ & _ & Hcap & Di & -> & Hi). apply in_app_or in Hb as [Hb|Hb].
  + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec.
    destruct Hb as [<- | []]. destruct Hcap as [(Hc0 & _) | (_ & Hl)]; [lia | exact Hl].
  + destruct (rm_items_in _ items kids Di b Hi Hb) as (i & u & D1 & Hil & HP & Hin).
    rewrite Forall_forall in IH. exact (IH u (nth_error_In items i Hil) m lblk _ D1 HP b Hin).
- destruct Hb2 as (_ & _ & _ & Hcap & Di & -> & Hi). apply in_app_or in Hb as [Hb|Hb].
  + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec.
    destruct Hcap as [(Hc0 & _) | (_ & Hk & Hy)]; [lia|].
    destruct Hb as [<- | [<- | []]]; [exact Hk | exact Hy].
  + destruct (rm_mems_in m lblk _ members kids keys Di b Hi Hb) as [(x & k & nm & -> & Hc) | (i & nm & u & D1 & Hil & HP & Hin)].
    * exact (proj1 Hc).
    * rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
      exact (IH m lblk _ D1 HP b Hin).
Qed.
Lemma rm_raw_of_aview : forall H H' (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS H' m' a = aview SEGS H m a -> mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn E. apply mbyte_of_aview in E. unfold mbyte in E. rewrite (seg_rom_none SEGS a Ha Hn) in E.
destruct (mrestrict H' m' (Z_to_bv 64 a)), (mrestrict H m (Z_to_bv 64 a)); congruence.
Qed.
(* the frame lemma across two worlds: a tree whose footprint is off the image and keeps its views *)
Lemma rm_node_move : forall (Wa Wb : world SEGS) ma mb lblk p t D,
  pj_nodeR SEGS (mrestrict (w_H Wa) ma) lblk p t D ->
  (forall x, pj_footR p D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ aview SEGS (w_H Wb) mb x = aview SEGS (w_H Wa) ma x) ->
  pj_nodeR SEGS (mrestrict (w_H Wb) mb) lblk p t D.
Proof.
intros Wa Wb ma mb lblk p t D H HF. apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wa) ma) _ lblk p D H).
apply rm_agree. intros x Hx. destruct (HF x Hx) as (Hr & Hn & E). exact (rm_raw_of_aview _ _ ma mb x Hr Hn E).
Qed.
Lemma rm_ro_img : forall a, in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
End gc.
Section gs. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma rm_region_nth : forall E ss ms i r,
  st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma rm_field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem segs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok segs E m b od w e v Hck He Hv Hw).
Qed.
Lemma rm_awr_cons : forall E r rs STK sp0 FP bl0 blc ly own n b,
  YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
  (forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
  awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. apply Hw. exact Ha.
- apply H. exists r'. auto.
Qed.
End gs.
Section pc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Lemma rm_slot_lt_ceil : forall k e, 0 <= k < 2 ^ 40 -> plookup pl_tpi k = Some e ->
  pa_val A_TEXT + k < YM05.alloc_ceiling.
Proof.
intros k e Hk40 Hk. pose proof pa_B_ok as HB. rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma L pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (Himg : in_img pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (pa_segs_low _ Himg) as HR.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia.
pose proof (@YM05.alloc_ceiling_value rc) as [[HC _] _]. unfold kLowMemEnd in HR. lia.
Qed.
Lemma rm_slot_lt_ceil_b : forall k, 0 <= k < 2 ^ 40 ->
  match plookup pl_tpi k with Some _ => true | None => false end = true ->
  pa_val A_TEXT + k < YM05.alloc_ceiling.
Proof.
intros k Hk H. destruct (plookup pl_tpi k) as [e|] eqn:He; [|discriminate H].
exact (rm_slot_lt_ceil k e Hk He).
Qed.
End pc.
(* a stretch over regions without write windows leaves the memory as it was (S6PjCommon.v gs_memeq) *)
Ltac rm_memeq HF EQ :=
let xx := fresh "xx" in let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
lazymatch type of HF with frame_of _ _ ?m ?m' =>
assert (EQ : m' = m) by (apply functional_extensionality; intros xx; apply HF; intros (rr & Hin & Hr);
  vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]);
  destruct Hin) end.
(* a stretch whose regions have no write window (S6PjCommon.v gs_awr0) *)
Ltac rm_awr0 :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
repeat (eapply rm_awr_cons; [reflexivity | reflexivity | cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; lia |]);
apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg B_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the allocator laws at the harness head length cf_head (the B' instance's laws PALibB.exvi_eh_laws are at cf_head):
   field 14 (alx_hshadow) is a harness block's user-bytes shadow, field 22 (alx_hhead) its head poison *)
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis TL : PALibCore (L := B_prog_listing) (PI := PA) B.
(* the callee texts, the texts of record (kit decff67d721f, PRH_FnPj.v) *)
Hypothesis PJ_GET : tpj_get_specX (cp := CP) (PI := prh_img_B) (PA := PA) B ARx SK.
Hypothesis PJ_GET_STR : tpj_get_str_specX (cp := CP) (PI := prh_img_B) (PA := PA) B ARx SK.
(* RM_IMG IS A FACT ABOUT THE ASYMS RECORD B (its as_owned_static, as_errno, as_const, as_zero_shadow) at this image,
   discharged at the #102 asyms instance of the image by vm_compute, as PALib is (B': RM_IMG_at_Bp in
   read_members_Bp.v). Per key: kept_img over the string and its NUL, and the PRESENCE of every shadow byte the
   string's shadow hull reads (shadow_hull_vis, YG0d.v:310): zero shadow or a const cell of ANY value - the window holds
   global redzones (0xf9 cells), so ro_shadow_ok there is false at B'. The table: kept_img over its six words. The
   zero ranges 8-aligned (zero_shadow_range's premise; aso_zshadow of asyms_ok, which AR_laws_x does not give). *)
Hypothesis RM_IMG : (forall k n, In (k, n) (rm_keys (PA := PA)) -> kept_img (PA := PA) B k (n + 1) /\
    (forall a, k / 64 * 64 <= a < (k + n) / 64 * 64 + 64 ->
       in_zs B (a - a mod 8) 8 \/ exists v, forall ly, In (z1 (ANum (shadow_addr a)) v) (as_const B ly))) /\
  kept_img (PA := PA) B (VAL (A_OBJ 3)) 48 /\
  Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* ---- the pure image facts of PA (the parametric form's own; each decided by vm_compute at PI_prog_B in the
   instance file): read_members' entry (DERIVED: slot 930), the shadow-base GOT word and cell in the image, the image
   start, the base the listing's literal offsets are added to, the thirteen keys' bytes and their 32-byte slots in the
   image, read_members.top's six words, and alloc.c's statics outside the read-only bytes ---- *)
Hypothesis rm_pa_ent : SIGMA AS_read_members = BASE + AF_rmB.
Hypothesis rm_pa_obj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
Hypothesis rm_pa_lo : @pa_lo _ _ PA = IMG_LO_B.
Hypothesis rm_pa_o2 : VAL (A_OBJ 2) = IMG_LO_B.
Hypothesis rm_pa_keys : forall off nm, In (off, nm) rm_keytab ->
  (forall j, (j <= length nm)%nat ->
     seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 2) + off + Z.of_nat j)) = Some (Z_to_bv 8 (nth j (nm ++ [0]) 0))) /\
  (forall j, 0 <= j < 32 -> seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 2) + off + j)) <> None).
Hypothesis rm_pa_top : forall i j, (i < 6)%nat -> (j < 8)%nat ->
  seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 3) + 8 * Z.of_nat i + Z.of_nat j)) =
  Some (Z_to_bv 8 (rm_byte (VAL (A_OBJ 2) + 0x11020 + 32 * Z.of_nat i) j)).
Hypothesis rm_pa_top_al : VAL (A_OBJ 3) mod 8 = 0.
Hypothesis rm_pa_pst : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a.

#[local] Notation STKR := (STK_read_members (PI := prh_img_B)).
Local Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
Lemma rm_stks : STKR = 8432 /\ STK_pj_get (PI := prh_img_B) = 8288 /\ STK_pj_get_str (PI := prh_img_B) = 8304.
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma rm_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
(* the hull of [x, x + n): every shadow byte it reads is the shadow byte of an address in [x / 64 * 64, (x + n - 1) / 64 * 64 + 64) *)
Lemma rm_hull_addr : forall x n s, 0 <= x -> 0 < n ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  exists a, x / 64 * 64 <= a < (x + n - 1) / 64 * 64 + 64 /\ shadow_addr a = s.
Proof.
intros x n s Hx Hn Hs. unfold shadow_addr in *. exists (8 * (s - SHADOW_OFF)). split.
- unfold SHADOW_OFF in *. split; [|]; lia.
- unfold SHADOW_OFF in *. lia.
Qed.

(* ======== the entry state: the binders and premises, fixed ======== *)
Section w.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : jv) (D Lam : list (Z * Z))
  (peak cnt fail ran most own : Z).
Hypothesis HFPRE : fpre (PA := PA) B ARx STKR ly S Hp W regs mem md ch.
Hypothesis H10 : getr regs 10 = w64 doc.
Hypothesis Hnode : pj_nodeR SEGS (rdW W mem) (prh_lin Lam) doc t D.
Hypothesis Hrs : PRH_FnPj.prhPj_rslot (PA := PA) B STKR ly S W regs mem doc.
Hypothesis HLED : prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own.

(* a later state of the walk: the journal from the entry, no fake frame, the same blocks *)
Definition rm_now (ly2 : alayout) (W2 : world SEGS) (mem2 : word -> option byte) (md2 : Model) (k : Z) : Prop :=
  AJ STKR (spZ regs) [] ly S Hp W mem md [] ly2 S Hp W2 mem2 md2 k /\ ablocks B ly2 S = ablocks B ly S.

Lemma rm_entry_ar : ARx ly S Hp W mem md.
Proof. destruct HFPRE as ((HAR & _) & _). exact HAR. Qed.
Lemma rm_entry_stk : astk_ok STKR ly (spZ regs).
Proof. destruct HFPRE as ((_ & _ & _ & _ & _ & Hstk & _) & _). exact Hstk. Qed.

(* a harness block of the ledger: its allocator block, its hidden head, its bounds *)
Lemma rm_lam_blk : forall a k, In (a, k) Lam ->
  0 <= k /\ 4096 <= a - 16 /\ a + k <= YM05.alloc_ceiling /\ In (a - 16, k + 16) (ablocks B ly S) /\ In (a - 16) Hp /\
  a mod 16 = 0 /\ in_app (a - 16) (k + 16) /\ (forall x, a - 16 <= x < a + k -> ~ in_img SEGS x).
Proof.
intros a k Hin. pose proof rm_entry_ar as HAR.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLED Hin) as (Hk0 & Hab & Hhp & Ham & _).
change (@cf_head CP) with 16 in *.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) HAR Hab) as (Hal & H4096 & Hc & Happ & _).
rewrite rm_req in Hc, Happ by lia.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact Ham|].
split; [exact Happ|].
intros x Hx. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) x HAR Hab). rewrite rm_req by lia. lia.
Qed.

(* a byte of a block of the tree keeps its view at every later state *)
Lemma rm_KD : forall ly2 W2 mem2 md2 k, rm_now ly2 W2 mem2 md2 k -> forall b x, In b D -> pj_holdsR b x ->
  0 <= x < YM05.alloc_ceiling /\ ~ in_img SEGS x /\ aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof.
intros ly2 W2 mem2 md2 k [HJ Eab] [bx bk] x Hb Hx. unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
pose proof (rm_nodeR_lblk t _ _ _ _ Hnode (bx, bk) Hb) as Hl. unfold prh_lin in Hl. cbn [fst snd] in Hl.
destruct (rm_lam_blk bx bk Hl) as (Hk0 & H4 & Hc & Hab & _ & _ & _ & Hni).
split; [lia|]. split; [apply Hni; lia|].
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Kblk & _).
replace x with ((bx - 16) + (x - (bx - 16))) by lia.
apply (Kblk (bx - 16) (bk + 16) (x - (bx - 16))); [exact Hab | rewrite Eab; exact Hab | rewrite rm_req by lia; lia |].
apply inFP_nil.
Qed.

(* the root's home at the entry, the hidden head excluded (LAWS' field 22 through hhead_not_addressable_x, against
   rslot's range_addressable) *)
Lemma rm_home :
  (exists b n, In (b, n) (ablocks B ly S) /\ b <= doc /\ doc + 56 <= b + req_size n /\ (In b Hp -> b + 16 <= doc)) \/
  (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= doc /\
     doc + 56 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
  (spZ regs <= doc /\ doc + 56 <= ly_top ly).
Proof.
pose proof rm_entry_ar as HAR.
destruct Hrs as (H4096 & Hplace & Hamr & Hwin & HRA & HHU).
destruct Hplace as [(b & n & Hin & Hb1 & Hb2) | [Hfr | Hst]]; [left | right; left; exact Hfr | right; right; exact Hst].
exists b, n. split; [exact Hin|]. split; [exact Hb1|]. split; [exact Hb2|].
intros Hbp. destruct (Z_le_gt_dec (b + 16) doc) as [Hle|Hgt]; [exact Hle|]. exfalso.
assert (Hh0 : b <= doc < b + @cf_head CP) by (change (@cf_head CP) with 16; lia).
exact (hhead_not_addressable_x _ _ _ LAWS ly S Hp W mem md b n doc 56 HAR Hin Hbp Hh0 ltac:(lia) HRA).
Qed.

(* a byte of the root's 56 bytes keeps its view at every later state *)
Lemma rm_hdr_kept : forall ly2 W2 mem2 md2 k, rm_now ly2 W2 mem2 md2 k -> forall x, doc <= x < doc + 56 ->
  0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof.
intros ly2 W2 mem2 md2 k [HJ Eab] x Hx. pose proof rm_entry_ar as HAR. pose proof rm_entry_stk as Hstk.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & Kceil & Kblk & _ & Kfrm & _).
destruct rm_home as [(b & n & Hin & Hb1 & Hb2 & _) | [(cid & pos & Hin & Hf1 & Hf2) | (Hs1 & Hs2)]].
- destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b n HAR Hin) as (_ & H4 & Hc & _).
  split; [lia|]. split; [apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b n x HAR Hin); lia|].
  replace x with (b + (x - b)) by lia. apply (Kblk b n (x - b) Hin); [rewrite Eab; exact Hin | lia | apply inFP_nil].
- destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as [_ Hfb].
  pose proof (proj1 (Forall_forall _ _) Hfb (cid, pos) Hin) as (Fb1 & Fb2). cbn [fst snd] in Fb1, Fb2.
  split; [lia|]. split; [apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos x HAR Hin); lia|].
  apply (Kfrm cid pos x Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply inFP_nil].
- split; [lia|]. split; [intros Hi; pose proof (@pa_segs_low _ _ PA x Hi); unfold kLowMemEnd in *; lia|].
  apply Kceil; lia.
Qed.

(* the root's tree at every later state *)
Lemma rm_root_node_now : forall ly2 W2 mem2 md2 k, rm_now ly2 W2 mem2 md2 k ->
  pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam) doc t D.
Proof.
intros ly2 W2 mem2 md2 k HN. apply (rm_node_move W W2 mem mem2 _ doc t D Hnode).
intros x [Hx | (b & Hb & Hx)].
- exact (rm_hdr_kept ly2 W2 mem2 md2 k HN x Hx).
- destruct (rm_KD ly2 W2 mem2 md2 k HN b x Hb Hx) as (Hr & Hni & He). pose proof (@YM05.alloc_ceiling_lt rc).
  split; [lia|]. split; assumption.
Qed.

(* a fake frame lies on a 64-byte boundary and spans whole 64-byte units when it can hold a node *)
Lemma rm_ffo : kFakeFramesOff mod 64 = 0 /\ Z.shiftl 1 kStackSizeLog mod 64 = 0.
Proof. split; vm_compute; reflexivity. Qed.
Lemma rm_frame_al : forall cid pos, 56 <= fs_frame_bytes cid ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0.
Proof.
intros cid pos H56. pose proof rm_entry_ar as HAR.
pose proof (lo_F_al _ (alx_layout_ok SEGS B ARx LAWS ly S Hp W mem md HAR)) as HF. unfold page_aligned in HF.
destruct rm_ffo as [F1 F2].
assert (Hc : 0 <= cid).
{ destruct (Z_le_gt_dec 0 cid) as [h|h]; [exact h|]. exfalso. unfold fs_frame_bytes in H56.
  rewrite Z.shiftl_div_pow2 in H56 by lia. assert (64 / 2 ^ (- cid) <= 32); [|lia].
  apply Z.div_le_upper_bound; [lia|]. assert (2 <= 2 ^ (- cid)); [|lia].
  replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
assert (Hb : fs_frame_bytes cid = 64 * 2 ^ cid) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; lia).
split; [|rewrite Hb, Z.mul_comm; apply Z.mod_mul; lia].
unfold frame_addr, fs_frame_off. rewrite Hb.
apply Z.mod_divide in F2 as [q Hq]; [|lia]. rewrite Hq.
replace (ly_F ly + (kFakeFramesOff + cid * (q * 64) + pos * (64 * 2 ^ cid)))
  with ((ly_F ly + kFakeFramesOff) + (cid * q + pos * 2 ^ cid) * 64) by ring.
rewrite Z.mod_add by lia. lia.
Qed.

(* every allocator block holds no head of another block *)
Lemma rm_nohead : forall b n, In (b, n) (ablocks B ly S) -> ~ In b Hp -> forall h, In h Hp -> ~ (b <= h < b + req_size n).
Proof.
intros b n Hin Hnb h Hh Hr. pose proof rm_entry_ar as HAR.
destruct (Z.eq_dec h b) as [->|Hne]; [exact (Hnb Hh)|].
pose proof (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HP.
apply (Permutation_in h HP) in Hh. apply in_map_iff in Hh as ([a k] & Eh & Hak). cbn [fst snd] in Eh.
change (@cf_head CP) with 16 in Eh.
destruct (rm_lam_blk a k Hak) as (Hk0 & _ & _ & Hab & _). rewrite Eh in Hab.
assert (Hne2 : (b, n) <> (h, k + 16)) by (intros E; injection E as E1 _; lia).
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b n h (k + 16) HAR Hin Hab Hne2) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (rm_req (k + 16)) in Hd by lia. lia.
Qed.

(* the root's shadow facts at every later state *)
Lemma rm_root_shadow_now : forall ly2 W2 mem2 md2 k, rm_now ly2 W2 mem2 md2 k ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF doc 56 /\ shadow_hull_vis (aview SEGS (w_H W2) mem2) doc 56.
Proof.
intros ly2 W2 mem2 md2 k [HJ Eab]. pose proof rm_entry_ar as HAR. pose proof rm_entry_stk as Hstk.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hrs as (H4096 & _ & Hamr & _ & HRA & HHU).
pose proof HJ as (HAR2 & Hlle & _ & _ & _ & _ & _ & _ & Kceil & Kblk & _ & Kfrm & _).
destruct rm_home as [(b & n & Hin & Hb1 & Hb2 & Hhd) | [(cid & pos & Hin & Hf1 & Hf2) | (Hs1 & Hs2)]].
- assert (Hin2 : In (b, n) (ablocks B ly2 S)) by (rewrite Eab; exact Hin).
  destruct (in_dec Z.eq_dec b Hp) as [Hbp | Hbp].
  + pose proof (Hhd Hbp) as Hb16.
    destruct (alx_hshadow _ _ _ LAWS ly2 S Hp W2 mem2 md2 b n HAR2 Hin2 Hbp) as [Hbs Hhv].
    change (@cf_head CP) with 16 in Hbs, Hhv. split.
    * eapply block_shadow_range; [exact Hbs | lia | lia].
    * apply (rm_hull_sub _ (b + 16) (req_size n - 16) doc 56); [apply Hhv; lia | lia | lia | lia].
  + destruct (alx_shadow SEGS B ARx LAWS ly2 S Hp W2 mem2 md2 b n HAR2 Hin2 (rm_nohead b n Hin Hbp)) as [Hbs Hhv].
    split.
    * eapply block_shadow_range; [exact Hbs | lia | lia].
    * apply (rm_hull_sub _ b (req_size n) doc 56); [exact Hhv | lia | lia | lia].
- assert (H56 : 56 <= fs_frame_bytes cid) by lia.
  destruct (rm_frame_al cid pos H56) as [Fa Fb].
  assert (KS : forall s, shadow_addr (frame_addr ly cid pos) <= s < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
    aview SEGS (w_H W2) mem2 s = aview SEGS (w_H W) mem s)
    by (intros s Hs; apply (Kfrm cid pos s Hin); [right; unfold in_zr; cbn [fst snd]; lia | apply inFP_nil]).
  split.
  + apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact HRA].
    intros x Hx. apply KS. unfold shadow_of_addr, shadow_addr. lia.
  + intros s Hs. destruct (rm_hull_addr doc 56 s ltac:(lia) ltac:(lia) Hs) as (a & Ha & Esa).
    rewrite KS by (rewrite <- Esa; unfold shadow_addr; lia). exact (HHU s Hs).
- destruct (stk_aligned_x SEGS B ARx LAWS ly S Hp W mem md HAR) as [Al1 Al2].
  destruct Hlle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
  assert (ZS : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> aview SEGS (w_H W2) mem2 (SHADOW_OFF + a / 8) = Some 0).
  { intros a Ha. apply (alx_zshadow_byte SEGS B ARx LAWS ly2 S Hp W2 mem2 md2 a HAR2). rewrite Elo, Ehi. exact Ha. }
  split.
  + intros x Hx. exists 0. split; [unfold shadow_of_addr; apply ZS; lia | left; reflexivity].
  + intros s Hs. destruct (rm_hull_addr doc 56 s ltac:(lia) ltac:(lia) Hs) as (a & Ha & Esa).
    rewrite <- Esa. unfold shadow_addr. rewrite ZS by lia. discriminate.
Qed.

(* the root's rslot at a callee's entry (sp = the entry sp - 128, its STK at most pj_get_str's) at every later state *)
Lemma rm_root_rslot_now : forall ly2 W2 mem2 md2 k (regsc : bvmap 5 word) STKc, rm_now ly2 W2 mem2 md2 k ->
  spZ regsc = spZ regs - 128 -> 0 <= STKc <= 8304 ->
  PRH_FnPj.prhPj_rslot (PA := PA) B STKc ly2 S W2 regsc mem2 doc.
Proof.
intros ly2 W2 mem2 md2 k regsc STKc HN Hspc HSTK.
pose proof rm_stks as (ER & _ & _).
pose proof Hrs as (H4096 & Hplace & Hamr & Hwin & _ & _).
destruct (rm_root_shadow_now ly2 W2 mem2 md2 k HN) as [HRA2 HHU2].
destruct HN as [HJ Eab]. pose proof HJ as (_ & Hlle & _).
destruct Hlle as (_ & _ & _ & _ & _ & HlF & _ & _ & Etop & _).
split; [exact H4096|]. split.
{ destruct Hplace as [(b & n & Hin & Hb) | [(cid & pos & Hin & Hb) | (Hs1 & Hs2)]].
  - left. exists b, n. rewrite Eab. split; [exact Hin | exact Hb].
  - right; left. exists cid, pos. unfold frame_addr. rewrite HlF. split; [exact Hin | exact Hb].
  - right; right. rewrite Hspc, Etop. lia. }
split; [exact Hamr|]. split; [|split; [exact HRA2 | exact HHU2]].
intros a Ha Hw. apply (Hwin a Ha). rewrite ER in *. lia.
Qed.

(* a node of the tree below the root: the tree at the entry, its blocks among the root's, its header in one of them *)
Definition rm_sub (p : Z) (v : jv) (Dv : list (Z * Z)) : Prop :=
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam) p v Dv /\ incl Dv D /\
  exists kd kc, In (kd, kc) D /\ kd <= p /\ p + 56 <= kd + kc.
Lemma rm_sub_foot : forall p v Dv, rm_sub p v Dv -> forall x, pj_footR p Dv x -> exists b, In b D /\ pj_holdsR b x.
Proof.
intros p v Dv (_ & Hinc & kd & kc & Hk & H1 & H2) x [Hx | (b & Hb & Hx)].
- exists (kd, kc). split; [exact Hk | unfold pj_holdsR; cbn [fst snd]; lia].
- exists b. split; [exact (Hinc b Hb) | exact Hx].
Qed.
Lemma rm_sub_now : forall p v Dv ly2 W2 mem2 md2 k, rm_sub p v Dv -> rm_now ly2 W2 mem2 md2 k ->
  pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam) p v Dv.
Proof.
intros p v Dv ly2 W2 mem2 md2 k Hs HN. apply (rm_node_move W W2 mem mem2 _ p v Dv (proj1 Hs)).
intros x Hx. destruct (rm_sub_foot p v Dv Hs x Hx) as (b & Hb & Hbx).
destruct (rm_KD ly2 W2 mem2 md2 k HN b x Hb Hbx) as (Hr & Hni & He). pose proof (@YM05.alloc_ceiling_lt rc).
split; [lia|]. split; assumption.
Qed.
(* a node read at a later state is a node of the tree at the entry *)
Lemma rm_sub_of : forall p v Dv ly1 W1 mem1 md1 k1, rm_now ly1 W1 mem1 md1 k1 ->
  pj_nodeR SEGS (rdW W1 mem1) (prh_lin Lam) p v Dv -> incl Dv D ->
  (exists kd kc, In (kd, kc) D /\ kd <= p /\ p + 56 <= kd + kc) -> rm_sub p v Dv.
Proof.
intros p v Dv ly1 W1 mem1 md1 k1 HN Hn Hinc Hk. split; [|split; [exact Hinc | exact Hk]].
apply (rm_node_move W1 W mem1 mem _ p v Dv Hn).
assert (Hs : forall x, pj_footR p Dv x -> exists b, In b D /\ pj_holdsR b x).
{ intros x [Hx | (b & Hb & Hx)].
  - destruct Hk as (kd & kc & Hk & H1 & H2). exists (kd, kc). split; [exact Hk | unfold pj_holdsR; cbn [fst snd]; lia].
  - exists b. split; [exact (Hinc b Hb) | exact Hx]. }
intros x Hx. destruct (Hs x Hx) as (b & Hb & Hbx).
destruct (rm_KD ly1 W1 mem1 md1 k1 HN b x Hb Hbx) as (Hr & Hni & He). pose proof (@YM05.alloc_ceiling_lt rc).
split; [lia|]. split; [exact Hni | symmetry; exact He].
Qed.
(* a node below the root: its rslot at a callee's entry at every later state *)
Lemma rm_sub_rslot_now : forall p v Dv ly2 W2 mem2 md2 k (regsc : bvmap 5 word) STKc, rm_sub p v Dv ->
  rm_now ly2 W2 mem2 md2 k -> spZ regsc = spZ regs - 128 -> 0 <= STKc <= 8304 ->
  PRH_FnPj.prhPj_rslot (PA := PA) B STKc ly2 S W2 regsc mem2 p.
Proof.
intros p v Dv ly2 W2 mem2 md2 k regsc STKc Hs HN Hspc HSTK.
pose proof rm_stks as (ER & _ & _). pose proof rm_entry_stk as Hstk.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hs as (_ & _ & kd & kc & Hk & H1 & H2).
pose proof (rm_nodeR_lblk t _ _ _ _ Hnode (kd, kc) Hk) as Hl. unfold prh_lin in Hl. cbn [fst snd] in Hl.
destruct (rm_lam_blk kd kc Hl) as (Hk0 & H4 & Hc & Hab & Hhp & Ham & Happ & _).
destruct HN as [HJ Eab]. pose proof HJ as (HAR2 & _).
assert (Hab2 : In (kd - 16, kc + 16) (ablocks B ly2 S)) by (rewrite Eab; exact Hab).
destruct (alx_hshadow _ _ _ LAWS ly2 S Hp W2 mem2 md2 (kd - 16) (kc + 16) HAR2 Hab2 Hhp) as [Hbs Hhv].
change (@cf_head CP) with 16 in Hbs, Hhv. rewrite rm_req in Hbs, Hhv by lia.
replace (kd - 16 + 16) with kd in Hbs, Hhv by lia. replace (kc + 16 - 16) with kc in Hbs, Hhv by lia.
split; [lia|]. split.
{ left. exists (kd - 16), (kc + 16). rewrite rm_req by lia. split; [exact Hab2 | lia]. }
split; [unfold amem_range; unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
  pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _]; lia|].
split; [intros a Ha Hw; rewrite ER in *; lia|].
split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
apply (rm_hull_sub _ kd kc p 56); [apply Hhv; lia | lia | lia | lia].
Qed.

(* the read-only view at every later state (the journal's image clause; alloc.c's statics are not read-only) *)
Lemma rm_rod_now : forall ly2 W2 mem2 md2 k, rm_now ly2 W2 mem2 md2 k ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W2) mem2).
Proof.
intros ly2 W2 mem2 md2 k [HJ _] a Hro Hno Her.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kimg & _).
rewrite (Kimg a (rm_ro_img a Hro) Hno Her (fun Hp => rm_pa_pst a Hp Hro) (fp_spares_closed [] a sink_closed_nil)).
destruct HFPRE as (_ & HROD & _). exact (HROD a Hro Hno Her).
Qed.

(* ======== RM-G1 and RM-G2 discharged from RM_IMG and the image facts, at any ARx state ======== *)
(* a granule a kept_img names has its shadow present, 0 or the addressable prefix *)
Lemma rm_ro_shadow : forall ly2 S2 Hp2 W2 mem2 md2 a, ARx ly2 S2 Hp2 W2 mem2 md2 -> ro_shadow_ok B a ->
  exists s, aview SEGS (w_H W2) mem2 (shadow_addr a) = Some s /\ (s = 0 \/ a mod 8 < s < 8).
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 a HAR [(q & m & Hin & Hq & Hqm) | (v & Hv & Hvr)].
- destruct RM_IMG as (_ & _ & HZA). pose proof (proj1 (Forall_forall _ _) HZA (q, m) Hin) as (Zq & Zm). cbn [fst snd] in Zq, Zm.
  pose proof (alx_zshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (q, m) HAR ltac:(unfold zero_shadow_ranges; right; exact Hin))
    as HZ. cbn [fst snd] in HZ.
  exists 0. split; [|left; reflexivity].
  assert (Ei : shadow_addr a = shadow_of_addr SHADOW_OFF q + (a / 8 - q / 8)) by (unfold shadow_addr, shadow_of_addr; lia).
  rewrite Ei. apply HZ. lia.
- pose proof (alx_const_cells SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 HAR) as HC.
  pose proof (proj1 (Forall_forall _ _) HC _ (Hv ly2)) as Hc. unfold cell_holds, z1, c1 in Hc. cbn [c_at c_val c_w aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
  exists v. split; [|lia]. rewrite Hc. f_equal. unfold le_byte. cbn [Z.of_nat]. rewrite Z.shiftr_0_r.
  rewrite !Z.mod_small; lia.
Qed.
(* a granule of a key's 64-byte window has its shadow byte present (zero shadow, or a const cell of any value: the
   global redzones' 0xf9 are cells too) *)
Lemma rm_cell_present : forall ly2 S2 Hp2 W2 mem2 md2 a, ARx ly2 S2 Hp2 W2 mem2 md2 ->
  in_zs B (a - a mod 8) 8 \/ (exists v, forall ly, In (z1 (ANum (shadow_addr a)) v) (as_const B ly)) ->
  aview SEGS (w_H W2) mem2 (shadow_addr a) <> None.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 a HAR [Hz | (v & Hv)].
- destruct (rm_ro_shadow ly2 S2 Hp2 W2 mem2 md2 a HAR (or_introl Hz)) as (s & Hs & _). rewrite Hs. discriminate.
- pose proof (alx_const_cells SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 HAR) as HC.
  pose proof (proj1 (Forall_forall _ _) HC _ (Hv ly2)) as Hc. unfold cell_holds, z1, c1 in Hc. cbn [c_at c_val c_w aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc. rewrite Hc. discriminate.
Qed.
Lemma rm_keytab_props : forall off nm, In (off, nm) rm_keytab ->
  0x11020 <= off <= 0x111a0 /\ off mod 32 = 0 /\ (1 <= length nm <= 10)%nat /\ Forall (fun c => 0 < c < 256) nm.
Proof.
intros off nm H. unfold rm_keytab in H.
repeat (destruct H as [H|H]; [injection H as <- <-; split; [lia|]; split; [reflexivity|]; split; [cbn; lia|];
  apply Forall_forall; intros c Hc; cbn in Hc; lia|]).
destruct H.
Qed.
Lemma rm_keys_tab : forall off nm, In (off, nm) rm_keytab -> In (VAL (A_OBJ 2) + off, Z.of_nat (length nm)) (rm_keys (PA := PA)).
Proof.
intros off nm H. unfold rm_keys. apply in_map_iff. exists (off, Z.of_nat (length nm)). split; [reflexivity|].
unfold rm_keytab in H.
repeat (destruct H as [H|H]; [injection H as <- <-; vm_compute; tauto|]).
destruct H.
Qed.
Lemma rm_nth_byte : forall (nm : list Z) j, Forall (fun c => 0 < c < 256) nm -> 0 <= nth j (nm ++ [0]) 0 < 256.
Proof.
intros nm j H. destruct (Nat.lt_ge_cases j (length (nm ++ [0]))) as [Hj|Hj].
- pose proof (nth_In (nm ++ [0]) 0 Hj) as Hin. apply in_app_or in Hin as [Hin|[<-|[]]]; [|lia].
  rewrite Forall_forall in H. specialize (H _ Hin). lia.
- rewrite nth_overflow by exact Hj. lia.
Qed.
(* RM-G1: a key literal is a C string with cstr_ok at any ARx state whose view agrees with the image's read-only bytes *)
Lemma rm_key_cstr : forall ly2 S2 Hp2 W2 mem2 md2, ARx ly2 S2 Hp2 W2 mem2 md2 ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W2) mem2) ->
  forall off nm, In (off, nm) rm_keytab -> cstr_ok (PA := PA) W2 mem2 (VAL (A_OBJ 2) + off) nm.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 HAR HROD off nm Hin.
pose proof (rm_keytab_props off nm Hin) as (Ho1 & Ho2 & Hl & Hnz).
destruct (rm_pa_keys off nm Hin) as [Hbytes Htail].
destruct RM_IMG as (HK & _ & _). destruct (HK _ _ (rm_keys_tab off nm Hin)) as [(Hk1 & Hk2 & Hk3) Hwin].
rewrite rm_pa_o2 in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
unfold IMG_LO_B in *.
assert (Hval : forall j, (j <= length nm)%nat ->
  aview SEGS (w_H W2) mem2 (0x10000 + off + Z.of_nat j) = Some (nth j (nm ++ [0]) 0)).
{ intros j Hj. destruct (Hk3 (0x10000 + off + Z.of_nat j) ltac:(lia)) as (Hro & Hno & Her & _).
  rewrite (HROD _ Hro Hno Her). rewrite Hbytes by exact Hj. cbn [option_map]. rewrite Z_to_bv_unsigned. f_equal.
  unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. apply rm_nth_byte. exact Hnz. }
split; [split|].
- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. split; [|apply rm_nth_byte; exact Hnz].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  pose proof (Hval j ltac:(lia)) as Hv.
  destruct (aview_byte SEGS (w_H W2) mem2 _ _ Hv) as (b & Hb & Hbv & _). rewrite Hb. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned, <- Hbv. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  cbn [Z.of_nat]. rewrite Z.shiftr_0_r. pose proof (rm_nth_byte nm j Hnz). rewrite !Z.mod_small; lia.
- apply Forall_forall. intros c Hc. rewrite Forall_forall in Hnz. specialize (Hnz c Hc). lia.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold YGcfStr.amem_range8; left; lia|].
  split; [|split].
  + intros x Hx. destruct (Hk3 x ltac:(lia)) as (_ & _ & _ & Hrsk).
    destruct (rm_ro_shadow ly2 S2 Hp2 W2 mem2 md2 x HAR Hrsk) as (s & Hs & Hok).
    exists s. split; [exact Hs | unfold saddr_ok; lia].
  + intros s Hs. destruct (rm_hull_addr (0x10000 + off) (Z.of_nat (length nm) + 1) s ltac:(lia) ltac:(lia) Hs) as (a & Ha & Esa).
    rewrite <- Esa. exact (rm_cell_present ly2 S2 Hp2 W2 mem2 md2 a HAR (Hwin a ltac:(lia))).
  + intros a Ha. unfold aview, mbyte. destruct (mrestrict (w_H W2) mem2 (Z_to_bv 64 a)) as [b|]; [discriminate|].
    pose proof (Htail (a - (0x10000 + off)) ltac:(lia)) as Ht. replace (0x10000 + off + (a - (0x10000 + off))) with a in Ht by lia.
    destruct (seg_rom SEGS (Z_to_bv 64 a)); [discriminate | exfalso; exact (Ht eq_refl)].
Qed.
(* RM-G2: read_members.top's six words and the shadow 0 of their granules at any ARx state with the read-only view *)
Lemma rm_top_at : forall ly2 S2 Hp2 W2 mem2 md2, ARx ly2 S2 Hp2 W2 mem2 md2 ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W2) mem2) ->
  forall i, (i < 6)%nat ->
  val_mem SEGS (rdW W2 mem2) (VAL (A_OBJ 3) + 8 * Z.of_nat i) 8 (VAL (A_OBJ 2) + 0x11020 + 32 * Z.of_nat i) /\
  aview SEGS (w_H W2) mem2 (shadow_addr (VAL (A_OBJ 3) + 8 * Z.of_nat i)) = Some 0.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 HAR HROD i Hi.
destruct RM_IMG as (_ & (Ht1 & Ht2 & Ht3) & _).
pose proof rm_pa_top_al as Hal. pose proof rm_pa_o2 as Ho2.
unfold IMG_LO_B in *.
split.
- intros kk Hkk.
  destruct (Ht3 (VAL (A_OBJ 3) + 8 * Z.of_nat i + Z.of_nat kk) ltac:(lia)) as (Hro & Hno & Her & _).
  pose proof (HROD _ Hro Hno Her) as Hv. rewrite (rm_pa_top i kk Hi Hkk) in Hv. cbn [option_map] in Hv.
  destruct (aview_byte SEGS (w_H W2) mem2 _ _ Hv) as (b & Hb & Hbv & _). rewrite Hb. f_equal.
  apply bv_eq. rewrite <- Hbv, !Z_to_bv_unsigned. f_equal.
  assert (Hv64 : 0 <= VAL (A_OBJ 2) + 69664 + 32 * Z.of_nat i < 2 ^ 64) by (rewrite Ho2; lia).
  unfold YO0f.le_byte, rm_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
  rewrite (Z.mod_small (VAL (A_OBJ 2) + 69664 + 32 * Z.of_nat i) (2 ^ 64)) by exact Hv64.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
- destruct (Ht3 (VAL (A_OBJ 3) + 8 * Z.of_nat i + 7) ltac:(lia)) as (_ & _ & _ & Hrsk).
  destruct (rm_ro_shadow ly2 S2 Hp2 W2 mem2 md2 _ HAR Hrsk) as (s & Hs & Hok).
  replace (shadow_addr (VAL (A_OBJ 3) + 8 * Z.of_nat i)) with (shadow_addr (VAL (A_OBJ 3) + 8 * Z.of_nat i + 7))
    by (unfold shadow_addr; lia).
  rewrite Hs. f_equal. lia.
Qed.

(* ======== a call of pj_get (G = false) or pj_get_str (G = true) from read_members' frame, by the text ======== *)
Definition rm_kres (G : bool) (m : word -> option byte) (o : Z) (tt : jv) (Dt : list (Z * Z)) (nm : list Z) (z : Z) : Prop :=
  if G then PRH_FnPj.prhPj_get_str_res (PA := PA) m (prh_lin Lam) o tt Dt nm z
  else PRH_FnPj.prhPj_get_res (PA := PA) m (prh_lin Lam) o tt Dt nm z.
Definition rm_stkc (G : bool) : Z := if G then STK_pj_get_str (PI := prh_img_B) else STK_pj_get (PI := prh_img_B).
Definition rm_asc (G : bool) : asym := if G then AS_pj_get_str else AS_pj_get.
(* the state after a call, as the walk continues from it *)
Definition rm_after (G : bool) (W2 : world SEGS) (regsc : bvmap 5 word) (memc : word -> option byte) (ly2 : alayout)
  (md2 : Model) (k : Z) (o : Z) (tt : jv) (Dt : list (Z * Z)) (nm : list Z) (W3 : world SEGS) (c3 : config) : Prop :=
  exists ly3 regs3 mem3 md3 k1,
    c3 = mkCfg (mkst regs3 (getr regsc 1) mem3 (seg_rom SEGS)) md3 /\
    rm_now ly3 W3 mem3 md3 (k + k1) /\
    AJ (rm_stkc G) (spZ regs - 128) [] ly2 S Hp W2 memc md2 [] ly3 S Hp W3 mem3 md3 k1 /\
    aregs_preserved regsc regs3 /\
    prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly3 S Hp W3 mem3 Lam peak cnt fail ran most own /\
    (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem3) /\
    (o = 0 /\ getr regs3 10 = w64 0 \/ o <> 0 /\ exists z, getr regs3 10 = w64 z /\ rm_kres G (rdW W3 mem3) o tt Dt nm z).
Lemma rm_call : forall (G : bool) W2 E ss ms ly2 md2 k o off nm (tt : jv) Dt r,
  st_ok SEGS E ss (restrict (w_H W2) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA (rm_asc G) ->
  rm_now ly2 W2 (ms_mem ms) md2 k ->
  spZ (ms_regs ms) = spZ regs - 128 ->
  getr (ms_regs ms) 3 = getr regs 3 -> getr (ms_regs ms) 4 = getr regs 4 ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + r) -> 0 <= r < 2 ^ 40 -> r mod 2 = 0 ->
  match plookup (@pl_tpi _ PL_rm_B) r with Some _ => true | None => false end = true ->
  (s0Z (ms_regs ms) < YM05.alloc_ceiling \/ ly_top ly - 16 <= s0Z (ms_regs ms) \/ getr (ms_regs ms) 8 = getr regs 8) ->
  getr (ms_regs ms) 10 = w64 o -> getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 2) + off) -> In (off, nm) rm_keytab ->
  (o = 0 \/ (o = doc /\ tt = t /\ Dt = D) \/ rm_sub o tt Dt) ->
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly2 S Hp W2 (ms_mem ms) Lam peak cnt fail ran most own ->
  SRr SEGS W2 (mkCfg ms md2) (rm_after G W2 (ms_regs ms) (ms_mem ms) ly2 md2 k o tt Dt nm).
Proof.
intros G W2 E ss ms ly2 md2 k o off nm tt Dt r HS Hrv Hpc HN Hsp Hg3 Hg4 Hra Hr1 Hr2 Hrl Hs0 Ha0 Ha1 Hkey HO HLED2.
pose proof HN as [HJ Eab]. pose proof HJ as (HAR2 & Hlle & _).
pose proof HFPRE as (HPRE & HROD & HTOP & HRAZ & HFRM).
pose proof HPRE as (HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof rm_stks as (FS & FS1 & FS2).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (pa_base_lo (PL := PL_rm_B) (PI := PA)) as HBLO. rewrite rm_pa_lo in HBLO. unfold IMG_LO_B in HBLO.
pose proof (@pa_B_ok _ _ PA) as HB.
destruct Hlle as (_ & _ & _ & _ & _ & HlF & _ & _ & Etop & Elo & Ehi & _).
assert (HROD1 : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W2) (ms_mem ms)))
  by exact (rm_rod_now ly2 W2 (ms_mem ms) md2 k HN).
assert (HTOP1 : spZ (ms_regs ms) + 64 <= ly_stk_hi ly2) by (rewrite Hsp, Ehi; lia).
assert (HRAZ1 : raZ (ms_regs ms) < YM05.alloc_ceiling).
{ unfold raZ. rewrite Hra. rewrite unsigned_lit_small by lia. exact (rm_slot_lt_ceil_b (PL := PL_rm_B) (PI := PA) r Hr1 Hrl). }
assert (HK1 : cstr_ok (PA := PA) W2 (ms_mem ms) (VAL (A_OBJ 2) + off) nm)
  by exact (rm_key_cstr ly2 S Hp W2 (ms_mem ms) md2 HAR2 HROD1 off nm Hkey).
assert (HO1 : forall STKc, 0 <= STKc <= 8304 ->
  o = 0 \/ pj_nodeR SEGS (rdW W2 (ms_mem ms)) (prh_lin Lam) o tt Dt /\
  PRH_FnPj.prhPj_rslot (PA := PA) B STKc ly2 S W2 (ms_regs ms) (ms_mem ms) o).
{ intros STKc HSc. destruct HO as [Ho0 | [(-> & -> & ->) | Hsub]]; [left; exact Ho0 | right | right].
  - split; [exact (rm_root_node_now ly2 W2 (ms_mem ms) md2 k HN)|].
    exact (rm_root_rslot_now ly2 W2 (ms_mem ms) md2 k (ms_regs ms) STKc HN Hsp HSc).
  - split; [exact (rm_sub_now o tt Dt ly2 W2 (ms_mem ms) md2 k Hsub HN)|].
    exact (rm_sub_rslot_now o tt Dt ly2 W2 (ms_mem ms) md2 k (ms_regs ms) STKc Hsub HN Hsp HSc). }
assert (HCH : exists chc, achain ly2 (aview SEGS (w_H W2) (ms_mem ms)) (spZ regs + -128) (s0Z (ms_regs ms)) chc).
{ destruct (Z.ltb_spec (s0Z (ms_regs ms)) YM05.alloc_ceiling) as [Hl|Hl]; [exists []; apply achain_low; exact Hl|].
  destruct Hs0 as [Hs0 | [Hs0 | Hs0]]; [lia | exists []; left; split; [right; left; rewrite Etop; exact Hs0 | reflexivity]|].
  exists ch.
  assert (E8 : s0Z (ms_regs ms) = s0Z regs) by (unfold s0Z; rewrite Hs0; reflexivity). rewrite E8.
  apply (achain_ly_top ly ly2); [exact Etop|].
  apply (achain_lower ly _ (spZ regs)); [|lia].
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & Kceil & _).
  apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. apply Kceil; lia. }
destruct HCH as (chc & HCH).
unfold rm_asc, rm_stkc, rm_kres, rm_after in *.
pose (STKc := if G then STK_pj_get_str (PI := prh_img_B) else STK_pj_get (PI := prh_img_B)).
destruct G; (eapply SRr_mono;
[ eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs W2 E ss ms STKR (spZ regs) [] ly S Hp W mem md [] ly2 S Hp md2 k
    STKc [] (-128) (getr (ms_regs ms) 1) _ _ HS Hrv HJ);
  [ lia | reflexivity | lia | unfold STKc; cbn iota beta; rewrite ?FS1, ?FS2; lia
  | unfold STKc; cbn iota beta; rewrite ?FS1, ?FS2; lia
  | rewrite Hg3; exact Hgp | rewrite Hg4; exact Htp | reflexivity
  | rewrite Hra; apply (ret_ok_codeptr_v (PI := PA)); [exact Hr1 | exact Hr2]
  | rewrite Hra; rewrite unsigned_lit_small by lia; lia
  | exact HCH
  | intros HPRE1; rewrite Hpc;
    first
    [ exact (PJ_GET_STR ly2 S Hp W2 (ms_regs ms) (ms_mem ms) md2 _ o (VAL (A_OBJ 2) + off) nm tt Dt Lam peak cnt fail ran most own
        (conj HPRE1 (conj HROD1 (conj HTOP1 (conj HRAZ1 HFRM)))) Ha0 Ha1
        (HO1 (STK_pj_get_str (PI := prh_img_B)) ltac:(rewrite FS2; lia)) HK1 HLED2)
    | exact (PJ_GET ly2 S Hp W2 (ms_regs ms) (ms_mem ms) md2 _ o (VAL (A_OBJ 2) + off) nm tt Dt Lam peak cnt fail ran most own
        (conj HPRE1 (conj HROD1 (conj HTOP1 (conj HRAZ1 HFRM)))) Ha0 Ha1
        (HO1 (STK_pj_get (PI := prh_img_B)) ltac:(rewrite FS1; lia)) HK1 HLED2) ]
  | intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| cbv beta; intros W3 c3 _ (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k1 & -> & HJ3 & HJc & HP3 & HQ3);
  destruct HQ3 as ((EHp & ES & Eab3 & HLED3 & _ & HRES) & HMN); subst Hp3 S3;
  exists ly3, regs3, mem3, md3, k1;
  split; [reflexivity|]; split; [split; [exact HJ3 | rewrite Eab3; exact Eab]|];
  split; [replace (spZ regs - 128) with (spZ regs + -128) by lia; exact HJc|];
  split; [exact HP3|]; split; [exact HLED3|]; split; [exact HMN|];
  destruct HRES as [(Ho0 & Hz) | (Hon & _ & z & Hz & Hres)]; [left; split; [exact Ho0 | exact Hz]|];
  right; split; [exact Hon|]; exists z; split; [exact Hz | exact Hres] ]).
Qed.

(* ======== the frame and the low memory across the walk ======== *)
(* the thirteen saved registers' slots (offset off the walk's sp, register): ra, s0 .. s11 *)
Definition rm_saves : list (Z * bv 5) :=
  [(120, 1%bv); (112, 8%bv); (104, 9%bv); (96, 18%bv); (88, 19%bv); (80, 20%bv); (72, 21%bv); (64, 22%bv);
   (56, 23%bv); (48, 24%bv); (40, 25%bv); (32, 26%bv); (24, 27%bv)].
Definition rm_frame (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
  Forall (fun sr => val_mem SEGS (rdW W2 mem2) (spZ regs - 128 + fst sr) 8 (bv_unsigned (getr regs (snd sr)))) rm_saves.
Lemma rm_sp_bounds : YM05.alloc_ceiling + STKR <= spZ regs /\ spZ regs + 64 <= 2 ^ 47 /\ spZ regs mod 16 = 0.
Proof.
pose proof rm_entry_stk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HFPRE as (_ & _ & HTOP & _). lia.
Qed.
Lemma rm_val_call : forall STKc W2 memc ly2 md2 ly3 W3 mem3 md3 k1 a n v, 0 <= STKc <= 8304 ->
  AJ STKc (spZ regs - 128) [] ly2 S Hp W2 memc md2 [] ly3 S Hp W3 mem3 md3 k1 ->
  spZ regs - 128 <= a -> a + Z.of_nat n <= spZ regs ->
  val_mem SEGS (rdW W2 memc) a n v -> val_mem SEGS (rdW W3 mem3) a n v.
Proof.
intros STKc W2 memc ly2 md2 ly3 W3 mem3 md3 k1 a n v HSc HJc H1 H2 Hv.
pose proof rm_sp_bounds as (B1 & B2 & B3). pose proof rm_stks as (ER & _ & _).
destruct HJc as (_ & _ & _ & _ & _ & _ & _ & _ & Kceil & _).
apply (val_mem_kept SEGS (w_H W2) (w_H W3) memc mem3 a n v); [|exact Hv].
intros kk Hkk. apply Kceil; rewrite ?ER in *; lia.
Qed.
Lemma rm_frame_call : forall STKc W2 memc ly2 md2 ly3 W3 mem3 md3 k1, 0 <= STKc <= 8304 ->
  AJ STKc (spZ regs - 128) [] ly2 S Hp W2 memc md2 [] ly3 S Hp W3 mem3 md3 k1 ->
  rm_frame W2 memc -> rm_frame W3 mem3.
Proof.
intros STKc W2 memc ly2 md2 ly3 W3 mem3 md3 k1 HSc HJc HF. unfold rm_frame in *. rewrite Forall_forall in *.
intros sr Hsr. specialize (HF sr Hsr).
assert (Ho : 24 <= fst sr <= 120) by (cbn in Hsr; repeat (destruct Hsr as [<- | Hsr]; [cbn; lia|]); destruct Hsr).
exact (rm_val_call STKc W2 memc ly2 md2 ly3 W3 mem3 md3 k1 (spZ regs - 128 + fst sr) 8 (bv_unsigned (getr regs (snd sr)))
  HSc HJc ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia) HF).
Qed.
Lemma rm_pst_low : forall a, Exists (in_zr a) PST -> 0 <= a < YM05.alloc_ceiling.
Proof.
intros a H. apply Exists_exists in H as (r & Hin & Hr). pose proof asan_consts as (C1 & _).
vm_compute in Hin. unfold in_zr in Hr.
repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
(* the ledger and the two PST cells at a memory that agrees with another below alloc_ceiling *)
Lemma rm_led_keep : forall ly2 W2 m m',
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly2 S Hp W2 m Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a) ->
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly2 S Hp W2 m' Lam peak cnt fail ran most own.
Proof.
intros ly2 W2 m m' HLd KL.
apply (prh_ledger_kept_aview B ly2 S Hp W2 m ly2 S Hp W2 m' Lam peak cnt fail ran most own HLd).
- intros a Ha. apply KL. exact (rm_pst_low a Ha).
- intros a k0 i Hin Hi. change (@cf_head CP) with 16.
  destruct (rm_lam_blk a k0 Hin) as (Hk0 & H4 & Hc & _). apply KL. lia.
- intros a k0 _ H. exact H.
- apply Permutation_refl.
Qed.
(* The post, named *)
Definition rm_Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' _ mem' _ =>
  Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
  (room_live_cf S -> room_live_cf S') /\
  pj_nodeR SEGS (rdW W' mem') (prh_lin Lam) doc t D.
Definition rm_goal : world SEGS -> config -> Prop :=
  fpostm (PI := prh_img_B) (PA := PA) B ARx SK STKR [] regs ly S Hp W mem md rm_Q.
(* the callee-saved registers (YG0d.v acallee_saved), as register names *)
Definition rm_allB : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma rm_aregs : forall (regsF : bvmap 5 word),
  (forall r : bv 5, In r rm_allB -> getr regsF r = getr regs r) -> aregs_preserved regs regsF.
Proof.
intros regsF H r Hr. apply H. unfold rm_allB. apply in_map. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [cbn; tauto .. |].
assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct H0 as [-> | H0]; [cbn; tauto|]). subst r. cbn; tauto.
Qed.
(* the return: the registers back, the journal from the entry, the keeps *)
Lemma rm_fin : forall W3 ly3 regsF memF mdF mat k,
  rm_now ly3 W3 memF mdF k ->
  (forall r : bv 5, In r rm_allB -> getr regsF r = getr regs r) -> getr regsF 1%bv = getr regs 1%bv ->
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly3 S Hp W3 memF Lam peak cnt fail ran most own ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memF) ->
  rm_goal W3 (mkCfg (mkst regsF (v_jalr (getr regsF 1%bv) 0) memF (seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros W3 ly3 regsF memF mdF mat k HN Hkept G1 HLEDF HMN.
pose proof HFPRE as ((HAR & Hra & _) & _).
unfold rm_goal, fpostm, fpost, apost_base_x, fQmn.
exists ly3, S, Hp, regsF, memF, (with_vm_backing (m_vm_lazy mdF) mat mdF), k.
split; [rewrite G1, Hra; reflexivity|].
destruct HN as [HJ Eab].
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)); exact HJ|].
split; [exact (rm_aregs regsF Hkept)|].
split; [|exact HMN].
unfold rm_Q. split; [reflexivity|]. split; [reflexivity|]. split; [exact Eab|]. split; [exact HLEDF|].
split; [intros H; exact H|].
exact (rm_root_node_now ly3 W3 memF mdF k (conj HJ Eab)).
Qed.

(* ======== the walk ======== *)
(* the entry seat: the own frame of 128 bytes below the entry sp (atom 2), the GOT word of the shadow base and the
   shadow-base cell (the base is atom 32) *)
Definition rm_regions0 : smem := [stack_region 128; got_regionP; bcell_regionP 32].
Definition rm_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_rm0 : sstate := mkSS AF_rmB sr_atoms rm_regions0 None rm_facts0.
Definition rm_E0 (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Definition RM_Bx0 : sv := SOff 32 0.
Definition RM_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma rm_entry_seat :
  st_ok_pi SEGS VAL (rm_E0 regs) ss_rm0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_rmB)) mem (seg_rom SEGS))) /\
  sh_ok SEGS RM_Bx0 [] (rm_E0 regs) (mrestrict (w_H W) mem).
Proof.
pose proof HFPRE as (HPRE & _). split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (palc_got_shadow B TL) in Kgot. rewrite (palc_cell B TL) in Kgot, Kcell.
pose proof (palc_got_cell B TL) as HgcD.
assert (HgL : forall i, 0 <= i < 8 -> 0 <= VAL (A_OBJ 0) + i < kLowMemEnd /\ 0 <= VAL (A_OBJ 12) + i < kLowMemEnd).
{ intros i Hi. destruct (rm_pa_obj i Hi) as [H1 H2]. split; apply (@pa_segs_low _ _ PA); assumption. }
destruct (HgL 0 ltac:(lia)) as [HgotR HcellR]. destruct (HgL 7 ltac:(lia)) as [HgotR7 HcellR7].
pose proof rm_stks as (FS & _ & _).
set (E := rm_E0 regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; unfold rm_E0; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold rm_E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold rm_E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
rewrite restrict_mkst_fx. unfold ss_rm0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rm_regions0, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 RM_Bx0 SHADOW_OFF);
    [cbn [sv_denot RM_Bx0]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold rm_regions0, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hceil C1 C2 C3 C4 C5 HgotR HcellR HgotR7 HcellR7 HgcD FS.
  unfold kLowMemEnd. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rm_facts0 f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
    revert Hslo Hshi H47 Hceil C1 FS Hstk0 Hal16; clear; intros; repeat split; lia|].
  split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
(* a callee-saved register r (its number z) back after a call (aregs_preserved HP) *)
Ltac rm_pres HP z r H :=
pose proof (HP z ltac:(unfold acallee_saved; lia)) as H; replace (Z_to_bv 5 z) with r in H by (apply bv_eq; reflexivity).


(* the own frame's writes (atom 2's window [sp - 128, sp)), the only writes of a stretch *)
Ltac rm_awr Usp :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
repeat (eapply rm_awr_cons; [reflexivity | first [exact Usp | reflexivity] |
  cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; first [lia | left; lia] | ]);
apply awr_ok_nil.

(* ---- the seats after a call: the frame of 128 bytes at the walk's sp (atom 2) with the thirteen saved registers as
   atoms 32 .. 44, the walk's own words (written window [sp, sp + 24)) as extra chunks, further regions; the env's
   atoms from 45 on are the extra values xs ---- *)
Definition rm_savechunks : list YP09.chunk :=
  [YP09.mkChunk 120 (CVal 8 (SOff 32 0)); YP09.mkChunk 112 (CVal 8 (SOff 33 0)); YP09.mkChunk 104 (CVal 8 (SOff 34 0));
   YP09.mkChunk 96 (CVal 8 (SOff 35 0)); YP09.mkChunk 88 (CVal 8 (SOff 36 0)); YP09.mkChunk 80 (CVal 8 (SOff 37 0));
   YP09.mkChunk 72 (CVal 8 (SOff 38 0)); YP09.mkChunk 64 (CVal 8 (SOff 39 0)); YP09.mkChunk 56 (CVal 8 (SOff 40 0));
   YP09.mkChunk 48 (CVal 8 (SOff 41 0)); YP09.mkChunk 40 (CVal 8 (SOff 42 0)); YP09.mkChunk 32 (CVal 8 (SOff 43 0));
   YP09.mkChunk 24 (CVal 8 (SOff 44 0))].
Definition rm_frame_region (extra : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 128 0 24 (rm_savechunks ++ extra).
Definition rm_Es (regsL : bvmap 5 word) (xs : list Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg regsL (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) xs)).
Lemma rm_Es_reg : forall regsL xs n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew (rm_Es regsL xs) n = getr regsL r.
Proof. intros regsL xs n r Hn Hr. unfold rm_Es. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regsL _ n r Hr). Qed.
Lemma rm_Es_save : forall regsL xs j sr, nth_error rm_saves j = Some sr -> ew (rm_Es regsL xs) (32 + j) = getr regs (snd sr).
Proof.
intros regsL xs j sr Hj. unfold rm_Es.
do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; rewrite Eimg_low by (unfold A_TEXT; lia);
  rewrite ew_Ereg_extra; reflexivity|]).
cbn in Hj. destruct j; cbn in Hj; discriminate Hj.
Qed.
Lemma rm_Es_x : forall regsL xs i, (i < length xs)%nat -> (i < 100)%nat ->
  ew (rm_Es regsL xs) (45 + i) = Z_to_bv 64 (nth i xs 0).
Proof.
intros regsL xs i Hi Hi100. unfold rm_Es. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (45 + i)%nat with (32 + (13 + i))%nat by lia. rewrite ew_Ereg_extra.
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map. change (length rm_saves) with 13%nat.
replace (13 + i - 13)%nat with i by lia.
rewrite (map_nth (Z_to_bv 64) xs 0 i). reflexivity.
Qed.
(* a register map with one register's expression replaced, when that register's value is the expression's *)
Lemma rm_regs_ok_set : forall E sr (regsL : bvmap 5 word) (r : bv 5) e,
  regs_ok E sr regsL -> getr regsL r = sv_denot E e -> regs_ok E (sr_set sr r e) regsL.
Proof.
intros E sr regsL r e H He r'. unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [apply H|].
pose proof (H r') as H'. unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact H'|].
rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx r') (ridx r)) as [Hi|Hi]; [|exact H'].
apply ridx_inj in Hi. subst r'. exact He.
Qed.
Lemma rm_seat_sr : forall regsL (WL : world SEGS) memL pc xs sr extra rs fs,
  regs_ok (rm_Es regsL xs) sr regsL ->
  getr regsL 2 = Z_to_bv 64 (spZ regs - 128) ->
  rm_frame WL memL ->
  (forall a, spZ regs - 128 <= a < spZ regs - 104 -> apresent (w_H WL) memL a) ->
  Forall (YP09.chunk_ok SEGS (rm_Es regsL xs) (rdW WL memL) (spZ regs - 128)) extra ->
  regions_wf (rm_frame_region extra :: rs) = true ->
  Forall (region_ok SEGS (rm_Es regsL xs) (rdW WL memL)) rs ->
  pairwise_disjoint (rm_Es regsL xs) (rm_frame_region extra :: rs) ->
  facts_ok (rm_Es regsL xs) fs ->
  st_ok_pi SEGS VAL (rm_Es regsL xs) (mkSS pc sr (rm_frame_region extra :: rs) None fs)
    (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + pc)) memL (seg_rom SEGS))).
Proof.
intros regsL WL memL pc xs sr extra rs fs Hsr H2 HF HP Hx Hwf Hrg Hpd Hfs.
pose proof rm_sp_bounds as (B1 & B2 & B3). pose proof rm_stks as (ER & _ & _).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [exact Hsr | exact Hwf | | exact Hpd | exact Hfs].
apply Forall_cons; [|exact Hrg].
assert (U2 : base_val (rm_Es regsL xs) (Some 2%nat) = spZ regs - 128).
{ cbn [base_val]. rewrite (rm_Es_reg regsL xs 2 2%bv) by (lia || reflexivity). rewrite H2. apply unsigned_lit_small. lia. }
unfold region_ok, rm_frame_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply HP; lia|].
apply Forall_app. split; [|exact Hx].
unfold rm_frame in HF. rewrite Forall_forall in HF.
unfold rm_savechunks. repeat apply Forall_cons; try apply Forall_nil.
all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?od (CVal 8 (SOff ?q 0))) =>
  let j := eval vm_compute in (q - 32)%nat in
  let srv := eval vm_compute in (nth j rm_saves (0, 0%bv)) in
  apply (chunk_ok_val SEGS _ _ _ od 8 (SOff q 0) (bv_unsigned (getr regs (snd srv))));
  [ cbn [sv_denot]; change q with (32 + j)%nat; rewrite (rm_Es_save regsL xs j srv) by reflexivity;
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 _)
  | cbn; lia
  | exact (HF srv ltac:(cbn [rm_saves In]; repeat first [left; reflexivity | right])) ] end.
Qed.
Lemma rm_seat : forall regsL (WL : world SEGS) memL pc xs extra rs fs,
  getr regsL 2 = Z_to_bv 64 (spZ regs - 128) ->
  rm_frame WL memL ->
  (forall a, spZ regs - 128 <= a < spZ regs - 104 -> apresent (w_H WL) memL a) ->
  Forall (YP09.chunk_ok SEGS (rm_Es regsL xs) (rdW WL memL) (spZ regs - 128)) extra ->
  regions_wf (rm_frame_region extra :: rs) = true ->
  Forall (region_ok SEGS (rm_Es regsL xs) (rdW WL memL)) rs ->
  pairwise_disjoint (rm_Es regsL xs) (rm_frame_region extra :: rs) ->
  facts_ok (rm_Es regsL xs) fs ->
  st_ok_pi SEGS VAL (rm_Es regsL xs) (mkSS pc sr_atoms (rm_frame_region extra :: rs) None fs)
    (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + pc)) memL (seg_rom SEGS))).
Proof. intros. apply rm_seat_sr; try assumption. unfold rm_Es. apply regs_ok_Eimg_Ereg. Qed.

(* the walk's invariant at a cut: the journal from the entry, the ledger (its g_most / g_own cells inside), the memory
   normal form, the frame's saved words *)
Definition rm_inv (ly2 : alayout) (W2 : world SEGS) (mem2 : word -> option byte) (md2 : Model) (k : Z) : Prop :=
  rm_now ly2 W2 mem2 md2 k /\
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly2 S Hp W2 mem2 Lam peak cnt fail ran most own /\
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) /\
  rm_frame W2 mem2.
(* across a call *)
Lemma rm_inv_call : forall G (W2 : world SEGS) memc ly2 md2 k (W3 : world SEGS) ly3 mem3 md3 k1,
  rm_inv ly2 W2 memc md2 k ->
  rm_now ly3 W3 mem3 md3 (k + k1) ->
  AJ (rm_stkc G) (spZ regs - 128) [] ly2 S Hp W2 memc md2 [] ly3 S Hp W3 mem3 md3 k1 ->
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly3 S Hp W3 mem3 Lam peak cnt fail ran most own ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem3) ->
  rm_inv ly3 W3 mem3 md3 (k + k1).
Proof.
intros G W2 memc ly2 md2 k W3 ly3 mem3 md3 k1 (HN & HLg & HM & HF) HN3 HJc HL3 HM3.
pose proof rm_stks as (_ & FS1 & FS2).
split; [exact HN3|]. split; [exact HL3|]. split; [intros h; exact (HM3 (HM h))|].
exact (rm_frame_call (rm_stkc G) W2 memc ly2 md2 ly3 W3 mem3 md3 k1 ltac:(unfold rm_stkc; destruct G; lia) HJc HF).
Qed.
(* a call by the text from an invariant state, to an invariant state at the return *)
Definition rm_ret (G : bool) (W2 : world SEGS) (regsc : bvmap 5 word) (memc : word -> option byte) (o : Z) (tt : jv)
  (Dt : list (Z * Z)) (nm : list Z) (W3 : world SEGS) (c3 : config) : Prop :=
  exists ly3 regs3 mem3 md3 k3,
    c3 = mkCfg (mkst regs3 (getr regsc 1) mem3 (seg_rom SEGS)) md3 /\ rm_inv ly3 W3 mem3 md3 k3 /\
    aregs_preserved regsc regs3 /\
    (forall a n v, spZ regs - 128 <= a -> a + Z.of_nat n <= spZ regs ->
       val_mem SEGS (rdW W2 memc) a n v -> val_mem SEGS (rdW W3 mem3) a n v) /\
    (o = 0 /\ getr regs3 10 = w64 0 \/ o <> 0 /\ exists z, getr regs3 10 = w64 z /\ rm_kres G (rdW W3 mem3) o tt Dt nm z).
Lemma rm_call_inv : forall (G : bool) W2 E ss ms ly2 md2 k o off nm (tt : jv) Dt r,
  st_ok SEGS E ss (restrict (w_H W2) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA (rm_asc G) ->
  rm_inv ly2 W2 (ms_mem ms) md2 k ->
  spZ (ms_regs ms) = spZ regs - 128 ->
  getr (ms_regs ms) 3 = getr regs 3 -> getr (ms_regs ms) 4 = getr regs 4 ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + r) -> 0 <= r < 2 ^ 40 -> r mod 2 = 0 ->
  match plookup (@pl_tpi _ PL_rm_B) r with Some _ => true | None => false end = true ->
  (s0Z (ms_regs ms) < YM05.alloc_ceiling \/ ly_top ly - 16 <= s0Z (ms_regs ms) \/ getr (ms_regs ms) 8 = getr regs 8) ->
  getr (ms_regs ms) 10 = w64 o -> getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 2) + off) -> In (off, nm) rm_keytab ->
  (o = 0 \/ (o = doc /\ tt = t /\ Dt = D) \/ rm_sub o tt Dt) ->
  SRr SEGS W2 (mkCfg ms md2) (rm_ret G W2 (ms_regs ms) (ms_mem ms) o tt Dt nm).
Proof.
intros G W2 E ss ms ly2 md2 k o off nm tt Dt r HS Hrv Hpc HI Hsp Hg3 Hg4 Hra Hr1 Hr2 Hrl Hs0 Ha0 Ha1 Hkey HO.
pose proof HI as (HN & HLd & _).
eapply SRr_mono; [exact (rm_call G W2 E ss ms ly2 md2 k o off nm tt Dt r HS Hrv Hpc HN Hsp Hg3 Hg4 Hra Hr1 Hr2 Hrl Hs0
  Ha0 Ha1 Hkey HO HLd)|].
intros W3 c3 _ (ly3 & regs3 & mem3 & md3 & k1 & -> & HN3 & HJc & HP & HL3 & HM3 & HR).
exists ly3, regs3, mem3, md3, (k + k1). split; [reflexivity|].
split; [exact (rm_inv_call G W2 (ms_mem ms) ly2 md2 k W3 ly3 mem3 md3 k1 HI HN3 HJc HL3 HM3)|].
split; [exact HP|]. split; [|exact HR].
intros a n v H1 H2 Hv.
exact (rm_val_call (rm_stkc G) W2 (ms_mem ms) ly2 md2 ly3 W3 mem3 md3 k1 a n v
  ltac:(pose proof rm_stks as (_ & FS1 & FS2); unfold rm_stkc; destruct G; lia) HJc H1 H2 Hv).
Qed.
(* across a stretch of the walk's own code: the new memory agrees outside the frame *)
Lemma rm_inv_run : forall ly2 W2 m md2 k m' md' k',
  rm_inv ly2 W2 m md2 k ->
  AJ STKR (spZ regs) [] ly S Hp W mem md [] ly2 S Hp W2 m' md' k' ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a) ->
  rm_frame W2 m' ->
  rm_inv ly2 W2 m' md' k'.
Proof.
intros ly2 W2 m md2 k m' md' k' ((HJ & Eab) & HLg & HM & HF) HJ' HM' KM HF'.
pose proof rm_sp_bounds as (B1 & B2 & B3). pose proof rm_stks as (ER & _ & _).
assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a)
  by (intros a Ha; pose proof (@YM05.alloc_ceiling_lt rc); apply KM; [lia | rewrite ER in B1; lia]).
split; [split; [exact HJ' | exact Eab]|]. split; [exact (rm_led_keep ly2 W2 m m' HLg KL)|]. split; [exact HM'|].
exact HF'.
Qed.
Lemma rm_savechunks_nth : forall j sr, nth_error rm_saves j = Some sr ->
  In (YP09.mkChunk (fst sr) (CVal 8 (SOff (32 + j) 0))) rm_savechunks.
Proof.
intros j sr Hj. do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]).
destruct j; cbn in Hj; discriminate Hj.
Qed.
(* the frame's saved words read back from a seat's frame region after a stretch *)
Lemma rm_frame_of_seat : forall E' (WL : world SEGS) memL cs,
  region_ok SEGS E' (rdW WL memL) (YP09.mkRegion (Some 2%nat) 0 128 0 24 cs) ->
  bv_unsigned (ew E' 2) = spZ regs - 128 ->
  incl rm_savechunks cs ->
  (forall j sr, nth_error rm_saves j = Some sr -> ew E' (32 + j) = getr regs (snd sr)) ->
  rm_frame WL memL.
Proof.
intros E' WL memL cs HR H2 Hinc HE. unfold rm_frame. rewrite Forall_forall. intros sr Hsr.
destruct (In_nth_error rm_saves sr Hsr) as (j & Hj).
apply (rm_field_of_region SEGS E' _ 2 (spZ regs - 128) cs 0 128 0 24 (fst sr) 8 (SOff (32 + j) 0)
  (bv_unsigned (getr regs (snd sr))) HR H2 (Hinc _ (rm_savechunks_nth j sr Hj))).
- cbn [sv_denot]. rewrite (HE j sr Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact (bv_unsigned_in_range 64 _).
- cbn. lia.
Qed.
(* a member pj_get found in an object is a node in one of the object's blocks *)
Lemma rm_res_node : forall m (tt : jv) Dt nm z o, pj_nodeR SEGS m (prh_lin Lam) o tt Dt ->
  PRH_FnPj.prhPj_get_res (PA := PA) m (prh_lin Lam) o tt Dt nm z ->
  z = 0 \/ exists v Dv, pj_nodeR SEGS m (prh_lin Lam) z v Dv /\ incl Dv Dt /\
    exists kd kc, In (kd, kc) Dt /\ kd <= z /\ z + 56 <= kd + kc.
Proof.
intros m tt Dt nm z o Hn3 Hres.
destruct tt as [| | | txt bits | s | items | members]; cbn [PRH_FnPj.prhPj_get_res] in Hres; try (left; exact Hres).
destruct Hres as [(_ & ->) | (i & v & kids & Di & Hnth & _ & Hkids & Ez & Hnz & Hinc)]; [left; reflexivity|right].
exists v, Di. split; [exact Hnz|]. split; [exact Hinc|].
cbn [pj_nodeR] in Hn3.
destruct Hn3 as (_ & _ & num' & str' & kids' & keys' & n' & cap' & Hh' & Es' & En' & Hcn' & Hcap' & Di' & ED' & HM').
pose proof Hh' as (_ & _ & _ & _ & (Hk0' & Hk') & _).
pose proof (rm_val8_uniq _ _ _ _ (proj2 Hkids) Hk' (proj1 Hkids) Hk0') as Ek. subst kids'.
assert (Hil : (i < length members)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
destruct Hcap' as [(Hc0 & _) | (Hcp & _)]; [lia|].
exists kids, (56 * cap'). split; [|lia].
rewrite ED'. destruct (Z.eqb_spec cap' 0) as [|_]; [lia|]. left. reflexivity.
Qed.
(* a member pj_get found below the root is a node of the tree *)
Lemma rm_get_sub : forall ly3 W3 mem3 md3 k3 nm z, rm_now ly3 W3 mem3 md3 k3 ->
  PRH_FnPj.prhPj_get_res (PA := PA) (rdW W3 mem3) (prh_lin Lam) doc t D nm z ->
  z = 0 \/ exists v Dv, rm_sub z v Dv.
Proof.
intros ly3 W3 mem3 md3 k3 nm z HN Hres.
destruct (rm_res_node _ t D nm z doc (rm_root_node_now ly3 W3 mem3 md3 k3 HN) Hres) as [Hz | (v & Dv & Hnz & Hinc & Hk)];
  [left; exact Hz | right].
exists v, Dv. exact (rm_sub_of z v Dv ly3 W3 mem3 md3 k3 HN Hnz Hinc Hk).
Qed.
(* the i-th item of an array node below the root is a node of the tree, at the array's kids word *)
Lemma rm_items_nth : forall (P : Z -> jv -> list (Z * Z) -> Prop) l a Dl i u,
  pj_itemsR P a l Dl -> nth_error l i = Some u -> exists Du, P (a + 56 * Z.of_nat i) u Du /\ incl Du Dl.
Proof.
intros P l. induction l as [|u0 r IH]; intros a Dl i u H Hi; [destruct i; discriminate Hi|].
cbn [pj_itemsR] in H. destruct H as (D1 & D2 & -> & H1 & H2).
destruct i as [|i]; cbn in Hi.
- injection Hi as <-. exists D1. split; [replace (a + 56 * Z.of_nat 0) with a by lia; exact H1 | intros b Hb; apply in_or_app; left; exact Hb].
- destruct (IH (a + 56) D2 i u H2 Hi) as (Du & HP & Hinc). exists Du.
  split; [replace (a + 56 * Z.of_nat (Datatypes.S i)) with (a + 56 + 56 * Z.of_nat i) by lia; exact HP|].
  intros b Hb. apply in_or_app. right. exact (Hinc b Hb).
Qed.
Lemma rm_item_sub : forall z1 items Dz i u, rm_sub z1 (JArr items) Dz -> nth_error items i = Some u ->
  exists kids1 Du, rd_u64 SEGS (rdW W mem) (z1 + 24) kids1 /\ rm_sub (kids1 + 56 * Z.of_nat i) u Du.
Proof.
intros z1 items Dz i u (Hn & Hinc & _) Hi. pose proof Hn as Hn'. cbn [pj_nodeR] in Hn'.
destruct Hn' as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hcn & Hcap & Di & ED & HI).
pose proof Hh as (_ & _ & _ & _ & Hkd & _).
assert (Hil : (i < length items)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
destruct Hcap as [(Hc0 & _) | (Hcp & Hlk)]; [lia|].
destruct (rm_items_nth _ items kids Di i u HI Hi) as (Du & Hnu & Hincu).
exists kids, Du. split; [exact Hkd|].
assert (HinD : incl Di Dz) by (rewrite ED; intros b Hb; apply in_or_app; right; exact Hb).
split; [exact Hnu|]. split; [intros b Hb; exact (Hinc b (HinD b (Hincu b Hb)))|].
exists kids, (56 * cap). split; [|lia]. apply Hinc. rewrite ED. destruct (Z.eqb_spec cap 0) as [|_]; [lia|]. left. reflexivity.
Qed.

(* a frame word written by the walk, read back from a seat's frame region after a stretch *)
Lemma rm_slot_of_region : forall E' m cs od e,
  region_ok SEGS E' m (YP09.mkRegion (Some 2%nat) 0 128 0 24 cs) -> bv_unsigned (ew E' 2) = spZ regs - 128 ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> val_mem SEGS m (spZ regs - 128 + od) 8 (bv_unsigned (sv_denot E' e)).
Proof.
intros E' m cs od e HR H2 Hin.
apply (rm_field_of_region SEGS E' m 2 (spZ regs - 128) cs 0 128 0 24 od 8 e _ HR H2 Hin).
- rewrite Z_to_bv_bv_unsigned. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact (bv_unsigned_in_range 64 _).
- cbn. lia.
Qed.
(* the walk's writes are inside its frame: every other byte keeps its view across a stretch *)
Lemma rm_keep_of_frame : forall E' rs (WL : world SEGS) m m',
  frame_of E' rs (rdW WL m) (rdW WL m') -> (forall a, in_wrange E' rs a -> spZ regs - 128 <= a < spZ regs) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) -> aview SEGS (w_H WL) m' a = aview SEGS (w_H WL) m a.
Proof.
intros E' rs WL m m' HF Hw a Ha Hn. unfold aview, mbyte.
rewrite (rm_mr_keep E' rs _ _ a HF); [reflexivity | | exact Ha]. intros Hin. exact (Hn (Hw a Hin)).
Qed.
(* the write windows of a seat's regions: only the frame (atom 2) has one, [sp, sp + 24) *)
Ltac rm_win U2 :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?ew_ewset_other in Hr by lia; rewrite ?U2 in Hr; lia|]);
destruct Hin.
Lemma rm_saves_lt : forall j srv, nth_error rm_saves j = Some srv -> (j < 13)%nat.
Proof.
intros j srv H. assert (Hn : nth_error rm_saves j <> None) by (rewrite H; discriminate).
apply nth_error_Some in Hn. exact Hn.
Qed.
(* the invariant after a stretch from a seat whose region 0 is the frame *)
Lemma rm_inv_after_run : forall E E' rs ly2 (W2 : world SEGS) m md2 k m' md' k' cs,
  rm_inv ly2 W2 m md2 k ->
  AJ STKR (spZ regs) [] ly S Hp W mem md [] ly2 S Hp W2 m' md' k' ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m') ->
  frame_of E rs (rdW W2 m) (rdW W2 m') ->
  (forall a, in_wrange E rs a -> spZ regs - 128 <= a < spZ regs) ->
  region_ok SEGS E' (rdW W2 m') (YP09.mkRegion (Some 2%nat) 0 128 0 24 cs) ->
  bv_unsigned (ew E' 2) = spZ regs - 128 ->
  incl rm_savechunks cs ->
  (forall j srv, nth_error rm_saves j = Some srv -> ew E' (32 + j) = getr regs (snd srv)) ->
  rm_inv ly2 W2 m' md' k'.
Proof.
intros E E' rs ly2 W2 m md2 k m' md' k' cs HI HJ' HM' HFr Hw HR U2 Hinc HE.
apply (rm_inv_run ly2 W2 m md2 k m' md' k' HI HJ' HM').
- exact (rm_keep_of_frame E rs W2 m m' HFr Hw).
- exact (rm_frame_of_seat E' W2 m' cs HR U2 Hinc HE).
Qed.
(* the frame region (region 0) of a state after a stretch *)
Ltac rm_frame_rg HS RG :=
let HSc := fresh "HSc" in pose proof HS as HSc; try unfold st_ok_pi, abs_ss in HSc;
lazymatch type of HSc with
| st_ok _ ?E' ?ss (restrict (w_H ?WL) ?msq) =>
  pose proof (rm_region_nth SEGS E' ss _ 0 _ HSc eq_refl) as RG; cbn [ms_mem restrict] in RG; clear HSc
end.
(* the invariant at the end of a stretch from a rm_Es seat: HI at the start, HJ HPM HFr from the run's post *)
Ltac rm_reinv HI HS HJ HPM HFr U2 HIn :=
let RG := fresh "RG" in rm_frame_rg HS RG;
lazymatch type of RG with region_ok _ ?E' (mrestrict (w_H ?WL) ?m') _ =>
eassert (HIn : rm_inv _ WL m' _ _);
[ eapply (rm_inv_after_run _ E' _ _ WL _ _ _ m' _ _ _ HI HJ HPM HFr);
  [ rm_win U2
  | exact RG
  | rewrite ?ew_ewset_other by lia; exact U2
  | let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn [rm_savechunks In] in Hc;
    repeat (destruct Hc as [<- | Hc]; [cbn [In]; repeat first [left; reflexivity | right]|]); destruct Hc
  | let j := fresh "j" in let srv := fresh "srv" in let Hj := fresh "Hj" in
    intros j srv Hj; pose proof (rm_saves_lt j srv Hj); rewrite ?ew_ewset_other by lia;
    apply rm_Es_save; exact Hj ]
| clear RG ] end.
(* a register's raw value after a stretch: the denotation of its expression in the seat's env *)
Ltac rm_rawreg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
Lemma rm_reg_U : forall E e (v : word) z, v = w64 z -> 0 <= z < 2 ^ 64 -> U E e = z -> v = sv_denot E e.
Proof. intros E e v z -> Hz HU. apply bv_eq. unfold U in HU. rewrite HU. unfold w64. apply unsigned_lit_small. exact Hz. Qed.
Lemma rm_U_reg : forall E e (v : word) z, v = sv_denot E e -> U E e = z -> 0 <= z < 2 ^ 64 -> v = w64 z.
Proof. intros E e v z -> HU Hz. apply bv_eq. unfold U in HU. rewrite HU. unfold w64. rewrite unsigned_lit_small; lia. Qed.
Lemma rm_afact : forall E n z lo hi al, bv_unsigned (ew E n) = z -> lo <= z <= hi -> z mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E n (mkAF lo hi al).
Proof. intros E n z lo hi al H H1 H2 H3. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H. repeat split; lia. Qed.
Lemma rm_ew_w64 : forall E n z, ew E n = w64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ew E n) = z.
Proof. intros E n z H Hz. rewrite H. unfold w64. apply unsigned_lit_small. exact Hz. Qed.
(* the shadow cell address of x as the instrumentation computes it: base + (x >> 3) *)
Definition rm_shx (nb nx : nat) : sv := SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SRL (SOff nx 0) (SLit 3)).
Lemma rm_shx_U : forall E nb nx x, bv_unsigned (ew E nb) = SHADOW_OFF -> bv_unsigned (ew E nx) = x -> 0 <= x < 2 ^ 47 ->
  U E (rm_shx nb nx) = SHADOW_OFF + x / 8.
Proof.
intros E nb nx x Hb Hx Hr. unfold rm_shx. rewrite U_SAlu, U_SAlu, !U_SOff, U_SLit, Hb, Hx, !Z.add_0_r.
cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small 3) by lia. change (Z.land 3 63) with 3.
rewrite (Z.mod_small x) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
unfold SHADOW_OFF in *. rewrite (Z.mod_small (x / 8)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
(* the six keys of read_members.top, in order *)
Lemma rm_top_key : forall i, (i < 6)%nat -> In (0x11020 + 32 * Z.of_nat i, snd (nth i rm_keytab (0, []))) rm_keytab.
Proof. intros i Hi. do 6 (destruct i as [|i]; [cbn; tauto|]). lia. Qed.

(* a node below the root lies in a harness block's user bytes *)
Lemma rm_sub_range : forall p v Dv, rm_sub p v Dv -> 4096 <= p /\ p + 56 <= YM05.alloc_ceiling.
Proof.
intros p v Dv (_ & _ & kd & kc & Hk & H1 & H2).
pose proof (rm_nodeR_lblk t _ _ _ _ Hnode (kd, kc) Hk) as Hl. unfold prh_lin in Hl. cbn [fst snd] in Hl.
destruct (rm_lam_blk kd kc Hl) as (Hk0 & H4 & Hc & _). lia.
Qed.
(* ======== the return ======== *)
Lemma rm_sv0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. apply bv_eq. rewrite denot_SOff, Z.add_0_r. unfold zcanon, M64. apply Z.mod_small.
exact (bv_unsigned_in_range 64 _).
Qed.
Lemma rm_fin_inv : forall W3 ly3 regsF memF mdF mat k,
  rm_inv ly3 W3 memF mdF k ->
  (forall r : bv 5, In r rm_allB -> getr regsF r = getr regs r) -> getr regsF 1%bv = getr regs 1%bv ->
  rm_goal W3 (mkCfg (mkst regsF (v_jalr (getr regsF 1%bv) 0) memF (seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros W3 ly3 regsF memF mdF mat k (HN & HLd & HM & _) Hk H1.
exact (rm_fin W3 ly3 regsF memF mdF mat k HN Hk H1 HLd HM).
Qed.
(* the registers at the ret of a rm_Es seat's epilogue: the saves from the frame's atoms 32 .. 44, sp + 128, gp and tp
   kept. ESAVE: the seat env's save atoms; U2: its sp atom; G3 / G4: its gp / tp *)
Ltac rm_retregs HS ESAVE U2 G3 G4 :=
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; unfold rm_allB in Hr; cbn [map] in Hr;
repeat (destruct Hr as [<- | Hr]; [
  lazymatch goal with |- getr _ (Z_to_bv 5 ?n) = _ =>
    let R := fresh "R" in rm_rawreg HS (Z_to_bv 5 n) R; rewrite R;
    lazymatch type of R with
    | _ = sv_denot _ (SOff 2%nat 128) =>
        apply bv_eq; rewrite denot_SOff, ?ew_ewset_other by lia; rewrite U2;
        unfold zcanon, M64; rewrite Z.mod_small by (pose proof rm_sp_bounds; lia);
        replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity);
        unfold spZ; lia
    | _ = sv_denot _ (SOff 3%nat 0) =>
        rewrite rm_sv0, ?ew_ewset_other by lia; replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity);
        exact G3
    | _ = sv_denot _ (SOff 4%nat 0) =>
        rewrite rm_sv0, ?ew_ewset_other by lia; replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity);
        exact G4
    | _ = sv_denot _ (SOff ?m 0) =>
        rewrite rm_sv0, ?ew_ewset_other by lia;
        let j := eval vm_compute in (m - 32)%nat in
        change m with (32 + j)%nat; rewrite (ESAVE j _ eq_refl); cbn [snd]; f_equal; apply bv_eq; reflexivity
    end
  end |]);
destruct Hr.
Ltac rm_retra HS ESAVE :=
let R := fresh "R" in rm_rawreg HS (1%bv : bv 5) R; rewrite R, rm_sv0, ?ew_ewset_other by lia;
change 32%nat with (32 + 0)%nat; rewrite (ESAVE 0%nat _ eq_refl); reflexivity.

(* ======== the tail (slot 136): pj_get_str (state, "encoding"), then pj_get_str (state, "bytes") if found; the return ==== *)
Definition rm_tailst (W2 : world SEGS) (regsL : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
  (ly2 : alayout) (k : Z) (z2 seen : Z) : Prop :=
  rm_inv ly2 W2 mem2 md2 k /\
  val_mem SEGS (rdW W2 mem2) (spZ regs - 128 + 16) 8 seen /\ 0 <= seen < 2 ^ 64 /\
  val_mem SEGS (rdW W2 mem2) (spZ regs - 128 + 8) 8 z2 /\
  getr regsL 2 = Z_to_bv 64 (spZ regs - 128) /\ getr regsL 3 = getr regs 3 /\ getr regsL 4 = getr regs 4 /\
  (z2 = 0 \/ exists v Dv, rm_sub z2 v Dv) /\ 0 <= z2 < 2 ^ 64.
Definition rm_factsT : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition rm_chT : list YP09.chunk := [YP09.mkChunk 8 (CVal 8 (SOff 45 0)); YP09.mkChunk 16 (CVal 8 (SOff 46 0))].
(* a seat of the tail and of the after-call states: the frame with the state word (atom 45) at sp + 8 and the counter
   (atom 46) at sp + 16 *)
Lemma rm_seatT : forall regsL (WL : world SEGS) memL ly2 mdL k pc z2 seen,
  rm_inv ly2 WL memL mdL k ->
  val_mem SEGS (rdW WL memL) (spZ regs - 128 + 16) 8 seen -> 0 <= seen < 2 ^ 64 ->
  val_mem SEGS (rdW WL memL) (spZ regs - 128 + 8) 8 z2 -> 0 <= z2 < 2 ^ 64 ->
  getr regsL 2 = Z_to_bv 64 (spZ regs - 128) ->
  st_ok_pi SEGS VAL (rm_Es regsL [z2; seen]) (mkSS pc sr_atoms [rm_frame_region rm_chT] None rm_factsT)
    (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + pc)) memL (seg_rom SEGS))).
Proof.
intros regsL WL memL ly2 mdL k pc z2 seen HI Hs Hs0 Hz Hz0 G2.
pose proof HI as ((HJ & _) & _ & _ & HFR).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kpres & _).
pose proof rm_stks as (FS & _ & _). pose proof rm_sp_bounds as (SB1 & SB2 & SB3).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
assert (E45 : ew (rm_Es regsL [z2; seen]) 45 = Z_to_bv 64 z2) by exact (rm_Es_x regsL [z2; seen] 0 ltac:(cbn; lia) ltac:(lia)).
assert (E46 : ew (rm_Es regsL [z2; seen]) 46 = Z_to_bv 64 seen) by exact (rm_Es_x regsL [z2; seen] 1 ltac:(cbn; lia) ltac:(lia)).
assert (U2 : bv_unsigned (ew (rm_Es regsL [z2; seen]) 2) = spZ regs - 128)
  by (rewrite (rm_Es_reg _ _ 2 2%bv) by (lia || reflexivity); rewrite G2; apply unsigned_lit_small; lia).
apply rm_seat; [exact G2 | exact HFR | intros a Ha; apply Kpres; rewrite FS; lia | | vm_compute; reflexivity | constructor
  | cbn [pairwise_disjoint all_disjoint]; exact (conj I I) |].
- constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val SEGS _ _ (spZ regs - 128) 8 8 (SOff 45 0) z2);
    [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hz].
  + apply (chunk_ok_val SEGS _ _ (spZ regs - 128) 16 8 (SOff 46 0) seen);
    [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hs].
- split; [|split; [exact I | exact I]]. cbn [rm_factsT f_atoms atoms_ok].
  split; [apply (rm_afact _ 2 (spZ regs - 128)); [exact U2 | lia | change (2 ^ 4) with 16; lia | lia]|]. exact I.
Qed.
Lemma rm_tail : forall W2 regsL mem2 md2 ly2 k z2 seen, rm_tailst W2 regsL mem2 md2 ly2 k z2 seen ->
  SRr SEGS W2 (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_rmB + 544))) mem2 (seg_rom SEGS)) md2) rm_goal.
Proof.
intros W2 regsL mem2 md2 ly2 k z2 seen (HI & Hseen & Hseen0 & Hz2v & G2 & G3 & G4 & Hz2s & Rz2).
pose proof rm_stks as (FS & FS1 & FS2). pose proof rm_sp_bounds as (SB1 & SB2 & SB3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
pose proof HI as ((HJ & Eab) & HLd & HPM & HFR).
pose proof (rm_seatT regsL W2 mem2 ly2 md2 k (AF_rmB + 544) z2 seen HI Hseen Hseen0 Hz2v Rz2 G2) as HS.
set (ET := rm_Es regsL [z2; seen]) in HS.
assert (ERT : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew ET n = getr regsL r)
  by (intros n r Hn Hr; exact (rm_Es_reg regsL [z2; seen] n r Hn Hr)).
assert (UT : bv_unsigned (ew ET 2) = spZ regs - 128)
  by (rewrite (ERT 2%nat 2%bv), G2 by (lia || reflexivity); apply unsigned_lit_small; lia).
assert (ET45 : ew ET 45 = Z_to_bv 64 z2) by exact (rm_Es_x regsL [z2; seen] 0 ltac:(cbn; lia) ltac:(lia)).
assert (ET243 : ew ET 243 = Z_to_bv 64 (VAL (A_OBJ 2))) by (subst ET; unfold rm_Es; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HEIT : img_env VAL A_LIM ET) by (subst ET; unfold rm_Es; apply Eimg_env).
assert (SHOKT : sh_ok SEGS (SOff 20 0) [] ET (mrestrict (w_H W2) mem2)) by constructor.
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_rm_B PA B PST ARx _ LAWS _ RLAW).
(* ---- slots 136 .. 140: a1 = "encoding", s0 = the state word, a0 = s0, the call pj_get_str (state, "encoding") ---- *)
paj_run_tok_x_inv RUN HS HJ SHOKT HPM RM_Bspan; [rm_awr UT|].
clear HG.
rm_reinv HI HS HJ HPM HFr UT HI1. clear HF HFr.
assert (HAET : env_agree 32 (Ereg regsL (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [z2; seen])) ET)
  by (split; [intros n Hn; subst ET; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS ET _ _ regsL _ [2%bv; 3%bv; 4%bv] HS HAET ltac:(vm_compute; reflexivity)) as KT.
prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msq) => rename msq into ms1 end.
assert (ET46 : ew ET 46 = Z_to_bv 64 seen) by exact (rm_Es_x regsL [z2; seen] 1 ltac:(cbn; lia) ltac:(lia)).
rm_frame_rg HS RG1.
pose proof (rm_slot_of_region ET _ _ 8 (SOff 45 0) RG1 UT ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hz21.
pose proof (rm_slot_of_region ET _ _ 16 (SOff 46 0) RG1 UT ltac:(cbn [In]; repeat first [left; reflexivity | right]))
  as Hseen1.
clear RG1.
rewrite rm_sv0, ET45, unsigned_lit_small in Hz21 by lia.
rewrite rm_sv0, ET46, unsigned_lit_small in Hseen1 by lia.
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs - 128)
  by (unfold spZ at 1; rewrite (KT 2%bv) by (cbn; tauto); rewrite G2; apply unsigned_lit_small; lia).
assert (HO2 : exists tt Dt, z2 = 0 \/ (z2 = doc /\ tt = t /\ Dt = D) \/ rm_sub z2 tt Dt)
  by (destruct Hz2s as [-> | (v2 & D2 & Hs2)]; [exists t, D; left; reflexivity | exists v2, D2; right; right; exact Hs2]).
destruct HO2 as (tt2 & Dt2 & HO2).
assert (Hz2c : z2 < YM05.alloc_ceiling)
  by (destruct Hz2s as [-> | (v2 & D2 & Hs2)]; [lia | pose proof (rm_sub_range z2 v2 D2 Hs2); lia]).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL_rm_B) (PI := PA)).
(* ---- the call pj_get_str (state, "encoding") (slot 140) ---- *)
eapply SRr_bind.
{ eapply (rm_call_inv true W2 ET _ ms1 ly2 _ _ z2 0x11180 [101; 110; 99; 111; 100; 105; 110; 103] tt2 Dt2 (AF_rmB + 564)
    HS eq_refl eq_refl HI1 Hsp1).
  - rewrite (KT 3%bv) by (cbn; tauto). exact G3.
  - rewrite (KT 4%bv) by (cbn; tauto). exact G4.
  - exact R1.
  - unfold AF_rmB, RMB_SLOT. lia.
  - unfold AF_rmB, RMB_SLOT. reflexivity.
  - vm_compute. reflexivity.
  - left. unfold s0Z. rewrite R8, ET45, unsigned_lit_small by lia. exact Hz2c.
  - rewrite R10, ET45. reflexivity.
  - pose proof (pa_val_range (A_OBJ 2)). rewrite R11, ET243, unsigned_lit_small by lia. reflexivity.
  - cbn [rm_keytab In]. repeat first [left; reflexivity | right].
  - exact HO2. }
cbv beta. intros W3 c3 _ (ly3 & regs3 & mem3 & md3 & k3 & -> & HI3 & HP3 & HKF3 & _).
rewrite R1.
rm_pres HP3 2 (2%bv : bv 5) P2. rm_pres HP3 3 (3%bv : bv 5) P3. rm_pres HP3 4 (4%bv : bv 5) P4.
rm_pres HP3 8 (8%bv : bv 5) P8.
assert (G3_2 : getr regs3 2 = Z_to_bv 64 (spZ regs - 128)) by (rewrite P2, (KT 2%bv) by (cbn; tauto); exact G2).
assert (G3_3 : getr regs3 3 = getr regs 3) by (rewrite P3, (KT 3%bv) by (cbn; tauto); exact G3).
assert (G3_4 : getr regs3 4 = getr regs 4) by (rewrite P4, (KT 4%bv) by (cbn; tauto); exact G4).
assert (G3_8 : getr regs3 8 = Z_to_bv 64 z2) by (rewrite P8, R8; exact ET45).
assert (Hseen3 : val_mem SEGS (rdW W3 mem3) (spZ regs - 128 + 16) 8 seen) by (apply HKF3; [lia | cbn; lia | exact Hseen1]).
assert (Hz23 : val_mem SEGS (rdW W3 mem3) (spZ regs - 128 + 8) 8 z2) by (apply HKF3; [lia | cbn; lia | exact Hz21]).
pose proof (rm_seatT regs3 W3 mem3 ly3 md3 k3 (AF_rmB + 564) z2 seen HI3 Hseen3 Hseen0 Hz23 Rz2 G3_2) as HS3.
set (E3 := rm_Es regs3 [z2; seen]) in HS3.
assert (ER3 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs3 r)
  by (intros n r Hn Hr; exact (rm_Es_reg regs3 [z2; seen] n r Hn Hr)).
assert (ESAVE3 : forall j srv, nth_error rm_saves j = Some srv -> ew E3 (32 + j) = getr regs (snd srv))
  by (intros j srv Hj; exact (rm_Es_save regs3 [z2; seen] j srv Hj)).
assert (U3 : bv_unsigned (ew E3 2) = spZ regs - 128)
  by (rewrite (ER3 2%nat 2%bv), G3_2 by (lia || reflexivity); apply unsigned_lit_small; lia).
assert (G33 : ew E3 3 = getr regs 3) by (rewrite (ER3 3%nat 3%bv) by (lia || reflexivity); exact G3_3).
assert (G34 : ew E3 4 = getr regs 4) by (rewrite (ER3 4%nat 4%bv) by (lia || reflexivity); exact G3_4).
assert (E3_243 : ew E3 243 = Z_to_bv 64 (VAL (A_OBJ 2))) by (subst E3; unfold rm_Es; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; unfold rm_Es; apply Eimg_env).
assert (SHOK3 : sh_ok SEGS (SOff 20 0) [] E3 (mrestrict (w_H W3) mem3)) by constructor.
pose proof HI3 as ((HJ3 & Eab3) & HLd3 & HPM3 & HFR3).
change (Z_to_bv 64 (BASE + 4284)) with (Z_to_bv 64 (BASE + (AF_rmB + 564))).
(* ---- slot 141: beqz a0 ---- *)
psrr_branch_tok RUN BR HS3 SHOK3 RM_Bspan.
- (* taken: no "encoding"; slots 147 .. 165: the counter, the volatile read, the frame back, ret *)
  paj_run_tok_x_inv RUN HS3 HJ3 SHOK3 HPM3 RM_Bspan; [rm_awr U3|].
  clear HG.
  rm_reinv HI3 HS3 HJ3 HPM3 HFr U3 HI4. clear HF HFr.
  eapply (RET W3 _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  apply (rm_fin_inv W3 _ _ _ _ mat' _ HI4).
  + rm_retregs HS3 ESAVE3 U3 G33 G34.
  + rm_retra HS3 ESAVE3.
- (* not taken: slots 142 .. 145: a1 = "bytes", a0 = the state word, the call pj_get_str (state, "bytes") *)
  paj_run_tok_x_inv RUN HS3 HJ3 SHOK3 HPM3 RM_Bspan; [rm_awr U3|].
  clear HG.
  rm_reinv HI3 HS3 HJ3 HPM3 HFr U3 HI4. clear HF HFr.
  assert (HAE3 : env_agree 32 (Ereg regs3 (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [z2; seen])) E3)
    by (split; [intros n Hn; subst E3; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof (regs_kept_of_st_ok SEGS E3 _ _ regs3 _ [2%bv; 3%bv; 4%bv; 8%bv] HS3 HAE3
    ltac:(vm_compute; reflexivity)) as KT3.
  prreg HS3 (1%bv : bv 5) S1. prreg HS3 (10%bv : bv 5) S10. prreg HS3 (11%bv : bv 5) S11.
  lazymatch type of HS3 with st_ok _ _ _ (restrict _ ?msq) => rename msq into ms4 end.
  rm_frame_rg HS3 RG4.
  assert (E3_45 : ew E3 45 = Z_to_bv 64 z2) by exact (rm_Es_x regs3 [z2; seen] 0 ltac:(cbn; lia) ltac:(lia)).
  assert (E3_46 : ew E3 46 = Z_to_bv 64 seen) by exact (rm_Es_x regs3 [z2; seen] 1 ltac:(cbn; lia) ltac:(lia)).
  pose proof (rm_slot_of_region E3 _ _ 8 (SOff 45 0) RG4 U3 ltac:(cbn [In]; repeat first [left; reflexivity | right]))
    as Hz24.
  pose proof (rm_slot_of_region E3 _ _ 16 (SOff 46 0) RG4 U3 ltac:(cbn [In]; repeat first [left; reflexivity | right]))
    as Hseen4.
  clear RG4.
  rewrite rm_sv0, E3_45, unsigned_lit_small in Hz24 by lia.
  rewrite rm_sv0, E3_46, unsigned_lit_small in Hseen4 by lia.
  assert (Hsp4 : spZ (ms_regs ms4) = spZ regs - 128)
    by (unfold spZ at 1; rewrite (KT3 2%bv) by (cbn; tauto); rewrite G3_2; apply unsigned_lit_small; lia).
  eapply SRr_bind.
  { eapply (rm_call_inv true W3 E3 _ ms4 ly3 _ _ z2 0x111a0 [98; 121; 116; 101; 115] tt2 Dt2 (AF_rmB + 584)
      HS3 eq_refl eq_refl HI4 Hsp4).
    - rewrite (KT3 3%bv) by (cbn; tauto). exact G3_3.
    - rewrite (KT3 4%bv) by (cbn; tauto). exact G3_4.
    - exact S1.
    - unfold AF_rmB, RMB_SLOT. lia.
    - unfold AF_rmB, RMB_SLOT. reflexivity.
    - vm_compute. reflexivity.
    - left. unfold s0Z. rewrite (KT3 8%bv), G3_8, unsigned_lit_small by (cbn; tauto || lia). exact Hz2c.
    - rewrite S10, (ER3 8%nat 8%bv), G3_8 by (lia || reflexivity). reflexivity.
    - pose proof (pa_val_range (A_OBJ 2)). rewrite S11, E3_243, unsigned_lit_small by lia. reflexivity.
    - cbn [rm_keytab In]. repeat first [left; reflexivity | right].
    - exact HO2. }
  cbv beta. intros W5 c5 _ (ly5 & regs5 & mem5 & md5 & k5 & -> & HI5 & HP5 & HKF5 & _).
  rewrite S1.
  rm_pres HP5 2 (2%bv : bv 5) Q2. rm_pres HP5 3 (3%bv : bv 5) Q3. rm_pres HP5 4 (4%bv : bv 5) Q4.
  assert (G5_2 : getr regs5 2 = Z_to_bv 64 (spZ regs - 128)) by (rewrite Q2, (KT3 2%bv) by (cbn; tauto); exact G3_2).
  assert (G5_3 : getr regs5 3 = getr regs 3) by (rewrite Q3, (KT3 3%bv) by (cbn; tauto); exact G3_3).
  assert (G5_4 : getr regs5 4 = getr regs 4) by (rewrite Q4, (KT3 4%bv) by (cbn; tauto); exact G3_4).
  assert (Hseen5 : val_mem SEGS (rdW W5 mem5) (spZ regs - 128 + 16) 8 seen)
    by (apply HKF5; [lia | cbn; lia | exact Hseen4]).
  assert (Hz25 : val_mem SEGS (rdW W5 mem5) (spZ regs - 128 + 8) 8 z2) by (apply HKF5; [lia | cbn; lia | exact Hz24]).
  pose proof (rm_seatT regs5 W5 mem5 ly5 md5 k5 (AF_rmB + 584) z2 seen HI5 Hseen5 Hseen0 Hz25 Rz2 G5_2) as HS5.
  set (E5 := rm_Es regs5 [z2; seen]) in HS5.
  assert (ER5 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E5 n = getr regs5 r)
    by (intros n r Hn Hr; exact (rm_Es_reg regs5 [z2; seen] n r Hn Hr)).
  assert (ESAVE5 : forall j srv, nth_error rm_saves j = Some srv -> ew E5 (32 + j) = getr regs (snd srv))
    by (intros j srv Hj; exact (rm_Es_save regs5 [z2; seen] j srv Hj)).
  assert (U5 : bv_unsigned (ew E5 2) = spZ regs - 128)
    by (rewrite (ER5 2%nat 2%bv), G5_2 by (lia || reflexivity); apply unsigned_lit_small; lia).
  assert (G53 : ew E5 3 = getr regs 3) by (rewrite (ER5 3%nat 3%bv) by (lia || reflexivity); exact G5_3).
  assert (G54 : ew E5 4 = getr regs 4) by (rewrite (ER5 4%nat 4%bv) by (lia || reflexivity); exact G5_4).
  assert (HEI5 : img_env VAL A_LIM E5) by (subst E5; unfold rm_Es; apply Eimg_env).
  assert (SHOK5 : sh_ok SEGS (SOff 20 0) [] E5 (mrestrict (w_H W5) mem5)) by constructor.
  pose proof HI5 as ((HJ5 & Eab5) & HLd5 & HPM5 & HFR5).
  change (Z_to_bv 64 (BASE + 4304)) with (Z_to_bv 64 (BASE + (AF_rmB + 584))).
  (* ---- slots 146 .. 165: the counter, the volatile read, the frame back, ret ---- *)
  paj_run_tok_x_inv RUN HS5 HJ5 SHOK5 HPM5 RM_Bspan; [rm_awr U5|].
  clear HG.
  rm_reinv HI5 HS5 HJ5 HPM5 HFr U5 HI6. clear HF HFr.
  eapply (RET W5 _ _ _ _ _ HS5 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  apply (rm_fin_inv W5 _ _ _ _ mat' _ HI6).
  + rm_retregs HS5 ESAVE5 U5 G53 G54.
  + rm_retra HS5 ESAVE5.
Qed.

(* ---- the loop head (slot 35) with i keys of read_members.top done ---- *)
Definition rm_topst (i : nat) (W2 : world SEGS) (regsL : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
  (ly2 : alayout) (k : Z) (z1 z2 seen : Z) : Prop :=
  rm_inv ly2 W2 mem2 md2 k /\
  val_mem SEGS (rdW W2 mem2) (spZ regs - 128 + 16) 8 seen /\ 0 <= seen < 2 ^ 64 /\
  getr regsL 2 = Z_to_bv 64 (spZ regs - 128) /\ getr regsL 3 = getr regs 3 /\ getr regsL 4 = getr regs 4 /\
  getr regsL 8 = w64 (- 8 * Z.of_nat i) /\ getr regsL 9 = w64 z1 /\ getr regsL 18 = w64 doc /\
  getr regsL 19 = w64 (VAL (A_OBJ 3) + 8 * Z.of_nat i) /\ getr regsL 20 = w64 SHADOW_OFF /\
  getr regsL 21 = w64 (SHADOW_OFF + (VAL (A_OBJ 3) + 8 * Z.of_nat i) / 8) /\ getr regsL 22 = w64 (-48) /\
  getr regsL 23 = w64 z2 /\
  (z1 = 0 \/ exists v Dv, rm_sub z1 v Dv) /\ (z2 = 0 \/ exists v Dv, rm_sub z2 v Dv) /\
  0 <= z1 < 2 ^ 64 /\ 0 <= z2 < 2 ^ 64.
(* ---- the state after the call pj_get (doc, "plugin") (slot 53): z4 its result; slot 8 holds z2 ---- *)
Definition rm_c4st (W2 : world SEGS) (regsL : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
  (ly2 : alayout) (k : Z) (z1 z2 z4 seen : Z) : Prop :=
  rm_inv ly2 W2 mem2 md2 k /\
  val_mem SEGS (rdW W2 mem2) (spZ regs - 128 + 16) 8 seen /\ 0 <= seen < 2 ^ 64 /\
  val_mem SEGS (rdW W2 mem2) (spZ regs - 128 + 8) 8 z2 /\
  getr regsL 2 = Z_to_bv 64 (spZ regs - 128) /\ getr regsL 3 = getr regs 3 /\ getr regsL 4 = getr regs 4 /\
  getr regsL 8 = w64 (-48) /\ getr regsL 9 = w64 z1 /\ getr regsL 18 = w64 doc /\ getr regsL 20 = w64 SHADOW_OFF /\
  getr regsL 10 = w64 z4 /\
  (z1 = 0 \/ exists v Dv, rm_sub z1 v Dv) /\ (z2 = 0 \/ exists v Dv, rm_sub z2 v Dv) /\
  (z4 = 0 \/ exists v Dv, rm_sub z4 v Dv) /\
  0 <= z1 < 2 ^ 64 /\ 0 <= z2 < 2 ^ 64 /\ 0 <= z4 < 2 ^ 64.

Lemma rm_w64_off : forall E n z c, ew E n = w64 z -> sv_denot E (SOff n c) = w64 (z + c).
Proof.
intros E n z c H. apply bv_eq. rewrite denot_SOff, H. unfold w64. rewrite !Z_to_bv_unsigned.
unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
(* a granule whose shadow byte is 0: its eight bytes are addressable *)
Lemma rm_ra_gran : forall (rd : Z -> option Z) a, a mod 8 = 0 -> rd (shadow_addr a) = Some 0 -> range_addressable rd SHADOW_OFF a 8.
Proof.
intros rd a Ha H x Hx. exists 0. split; [|unfold saddr_ok; lia].
replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr a) by (unfold shadow_of_addr, shadow_addr; lia). exact H.
Qed.
Definition rm_topP (i : nat) : Prop := forall W2 regsL mem2 md2 ly2 k z1 z2 seen,
  rm_topst i W2 regsL mem2 md2 ly2 k z1 z2 seen ->
  SRr SEGS W2 (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_rmB + 140))) mem2 (seg_rom SEGS)) md2) rm_goal.
(* the loop head's seat: atom 45 = top + 8 i, 46 = the key's address, 47 = the counter word at sp + 16, 48 = the shadow
   cell of top[i]. The cell is a region whose byte is 0 (RM-G2): the token engine cannot take this check, because its
   report path starts with an auipc pair, which its decoder does not read. *)
Definition rm_xs35 (i : nat) (seen : Z) : list Z :=
  [VAL (A_OBJ 3) + 8 * Z.of_nat i; VAL (A_OBJ 2) + 0x11020 + 32 * Z.of_nat i; seen;
   SHADOW_OFF + (VAL (A_OBJ 3) + 8 * Z.of_nat i) / 8].
Definition rm_sr35 : list sv := sr_set (sr_set sr_atoms 19%bv (SOff 45 0)) 21%bv (SOff 48 0).
Definition rm_topreg : YP09.region := YP09.mkRegion (Some 45%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 46 0))].
Definition rm_cellreg (n : nat) : YP09.region := YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition rm_facts35 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
(* a shadow byte 0 as a one-byte region's contents *)
Lemma rm_val1 : forall (H : word -> bool) m a, aview SEGS H m a = Some 0 -> val_mem SEGS (mrestrict H m) a 1 0.
Proof.
intros H m a Hv kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (aview_byte SEGS H m _ _ Hv) as (b & Hb & Hbv & _). rewrite Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned, <- Hbv. reflexivity.
Qed.
(* a byte range of a node below the root keeps its contents at every later state *)
Lemma rm_sub_val : forall p v Dv ly2 (W2 : world SEGS) mem2 md2 k a n x, rm_sub p v Dv -> rm_now ly2 W2 mem2 md2 k ->
  p <= a -> a + Z.of_nat n <= p + 56 -> val_mem SEGS (rdW W mem) a n x -> val_mem SEGS (rdW W2 mem2) a n x.
Proof.
intros p v Dv ly2 W2 mem2 md2 k a n x Hs HN H1 H2 Hv.
apply (val_mem_kept SEGS (w_H W) (w_H W2) mem mem2 a n x); [|exact Hv].
intros kk Hkk. destruct (rm_sub_foot p v Dv Hs (a + kk) ltac:(left; lia)) as (b & Hb & Hbx).
destruct (rm_KD ly2 W2 mem2 md2 k HN b (a + kk) Hb Hbx) as (_ & _ & He). exact He.
Qed.
(* an array node below the root: its kids word, its count, its tag, its alignment, its block *)
Lemma rm_arr_info : forall z1 items D1, rm_sub z1 (JArr items) D1 ->
  exists kids cap, rd_u64 SEGS (rdW W mem) (z1 + 24) kids /\ rd_u64 SEGS (rdW W mem) (z1 + 40) (Z.of_nat (length items)) /\
    rd_u32 SEGS (rdW W mem) z1 5 /\ z1 mod 8 = 0 /\ Z.of_nat (length items) <= cap /\
    (cap = 0 /\ kids = 0 \/ 0 < cap /\ 4096 <= kids /\ kids + 56 * cap <= YM05.alloc_ceiling).
Proof.
intros z1 items D1 (Hn & _). cbn [pj_nodeR] in Hn.
destruct Hn as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hcn & Hcap & _).
destruct Hh as ((Hal & _) & Hty & _ & _ & Hk & _ & Hnn & _). subst n.
exists kids, cap. split; [exact Hk|]. split; [exact Hnn|]. split; [exact Hty|]. split; [exact Hal|]. split; [lia|].
destruct Hcap as [Hc0 | (Hc0 & Hl)]; [left; exact Hc0|right]. unfold prh_lin in Hl.
destruct (rm_lam_blk kids (56 * cap) Hl) as (_ & H4 & Hc & _). lia.
Qed.
(* the shadow cell address base + ((x + c) >> 3), the operand order of the instrumentation *)
Definition rm_shxc (nb nx : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff nx c) (SLit 3)) (SOff nb 0).
Lemma rm_shxc_U : forall E nb nx c x, bv_unsigned (ew E nb) = SHADOW_OFF -> bv_unsigned (ew E nx) + c = x ->
  0 <= x < 2 ^ 47 -> U E (rm_shxc nb nx c) = SHADOW_OFF + x / 8.
Proof.
intros E nb nx c x Hb Hx Hr. unfold rm_shxc. rewrite U_SAlu, U_SAlu, !U_SOff, U_SLit, Hb, Hx, !Z.add_0_r.
cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small 3) by lia. change (Z.land 3 63) with 3.
rewrite (Z.mod_small x) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
unfold SHADOW_OFF in *. rewrite (Z.mod_small (x / 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* ======== the params loop head (slot 84) with j items done ======== *)
Definition rm_parst (j : nat) (W2 : world SEGS) (regsL : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
  (ly2 : alayout) (k : Z) (z1 z2 seen : Z) (items : list jv) (D1 : list (Z * Z)) (kids : Z) : Prop :=
  rm_inv ly2 W2 mem2 md2 k /\
  val_mem SEGS (rdW W2 mem2) (spZ regs - 128 + 16) 8 seen /\ 0 <= seen < 2 ^ 64 /\
  val_mem SEGS (rdW W2 mem2) (spZ regs - 128 + 8) 8 z2 /\ (z2 = 0 \/ exists v Dv, rm_sub z2 v Dv) /\ 0 <= z2 < 2 ^ 64 /\
  rm_sub z1 (JArr items) D1 /\ rd_u64 SEGS (rdW W mem) (z1 + 24) kids /\ (j <= length items)%nat /\
  getr regsL 2 = Z_to_bv 64 (spZ regs - 128) /\ getr regsL 3 = getr regs 3 /\ getr regsL 4 = getr regs 4 /\
  getr regsL 8 = w64 (VAL (A_OBJ 2) + 0x11140) /\ getr regsL 9 = w64 z1 /\ getr regsL 18 = w64 (z1 + 24) /\
  getr regsL 19 = w64 (z1 + 40) /\ getr regsL 20 = w64 (SHADOW_OFF + (z1 + 24) / 8) /\
  getr regsL 21 = w64 (VAL (A_OBJ 2) + 0x11160) /\ getr regsL 22 = w64 (SHADOW_OFF + z1 / 8) /\
  getr regsL 23 = w64 5 /\ getr regsL 24 = w64 (56 * Z.of_nat j) /\ getr regsL 25 = w64 (Z.of_nat j) /\
  getr regsL 27 = w64 (SHADOW_OFF + (z1 + 40) / 8).
Definition rm_parP (n : nat) : Prop := forall j W2 regsL mem2 md2 ly2 k z1 z2 seen items D1 kids,
  (length items - j = n)%nat -> rm_parst j W2 regsL mem2 md2 ly2 k z1 z2 seen items D1 kids ->
  SRr SEGS W2 (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_rmB + 336))) mem2 (seg_rom SEGS)) md2) rm_goal.

(* the seat with the params node: atoms 45 = the state word, 46 = the counter, 47 = the shadow base, 48 = the node's
   type word, 49 = its kids word, 50 = its count; region 1 the node's header (type, kids, count) *)
Definition rm_nodereg (tv : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 56 0 0
    [YP09.mkChunk 0 (CVal 4 tv); YP09.mkChunk 24 (CVal 8 (SOff 49 0)); YP09.mkChunk 40 (CVal 8 (SOff 50 0))].
Definition rm_xsN (z2 seen ty kids n : Z) : list Z := [z2; seen; SHADOW_OFF; ty; kids; n].
Definition rm_factsN (nB : nat) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 4096 (2 ^ 47 - 2 ^ 20) 3); (nB, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Lemma rm_seatN : forall regsL (WL : world SEGS) memL ly2 mdL k pc z2 seen z1 ty kids n tv sr nB,
  rm_inv ly2 WL memL mdL k ->
  val_mem SEGS (rdW WL memL) (spZ regs - 128 + 16) 8 seen -> 0 <= seen < 2 ^ 64 ->
  val_mem SEGS (rdW WL memL) (spZ regs - 128 + 8) 8 z2 -> 0 <= z2 < 2 ^ 64 ->
  getr regsL 2 = Z_to_bv 64 (spZ regs - 128) -> getr regsL 9 = w64 z1 ->
  4096 <= z1 -> z1 + 56 <= YM05.alloc_ceiling -> z1 mod 8 = 0 ->
  rd_u32 SEGS (rdW WL memL) z1 ty -> rd_u64 SEGS (rdW WL memL) (z1 + 24) kids -> rd_u64 SEGS (rdW WL memL) (z1 + 40) n ->
  sv_denot (rm_Es regsL (rm_xsN z2 seen ty kids n)) tv = Z_to_bv 64 ty ->
  regs_ok (rm_Es regsL (rm_xsN z2 seen ty kids n)) sr regsL ->
  bv_unsigned (ew (rm_Es regsL (rm_xsN z2 seen ty kids n)) nB) = SHADOW_OFF ->
  st_ok_pi SEGS VAL (rm_Es regsL (rm_xsN z2 seen ty kids n))
    (mkSS pc sr [rm_frame_region rm_chT; rm_nodereg tv] None (rm_factsN nB))
    (restrict (w_H WL) (mkst regsL (Z_to_bv 64 (BASE + pc)) memL (seg_rom SEGS))).
Proof.
intros regsL WL memL ly2 mdL k pc z2 seen z1 ty kids n tv sr nB HI Hs Hs0 Hz Hz0 G2 G9 Z1 Z2 Z3 Hty Hk Hn Htv Hsr HB.
pose proof HI as ((HJ & _) & _ & _ & HFR).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kpres & _).
pose proof rm_stks as (FS & _ & _). pose proof rm_sp_bounds as (SB1 & SB2 & SB3).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
set (E := rm_Es regsL (rm_xsN z2 seen ty kids n)).
assert (E45 : ew E 45 = Z_to_bv 64 z2) by exact (rm_Es_x regsL (rm_xsN z2 seen ty kids n) 0 ltac:(cbn; lia) ltac:(lia)).
assert (E46 : ew E 46 = Z_to_bv 64 seen) by exact (rm_Es_x regsL (rm_xsN z2 seen ty kids n) 1 ltac:(cbn; lia) ltac:(lia)).
assert (E49 : ew E 49 = Z_to_bv 64 kids) by exact (rm_Es_x regsL (rm_xsN z2 seen ty kids n) 4 ltac:(cbn; lia) ltac:(lia)).
assert (E50 : ew E 50 = Z_to_bv 64 n) by exact (rm_Es_x regsL (rm_xsN z2 seen ty kids n) 5 ltac:(cbn; lia) ltac:(lia)).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 128)
  by (subst E; rewrite (rm_Es_reg _ _ 2 2%bv) by (lia || reflexivity); rewrite G2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = z1)
  by (subst E; rewrite (rm_Es_reg _ _ 9 9%bv) by (lia || reflexivity); rewrite G9; unfold w64; apply unsigned_lit_small; lia).
destruct Hty as (Hty0 & Hty). destruct Hk as (Hk0 & Hk). destruct Hn as (Hn0 & Hn).
apply rm_seat_sr; [exact Hsr | exact G2 | exact HFR | intros a Ha; apply Kpres; rewrite FS; lia | | vm_compute; reflexivity | | |].
- change (rm_Es regsL (rm_xsN z2 seen ty kids n)) with E. constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val SEGS _ _ (spZ regs - 128) 8 8 (SOff 45 0) z2);
    [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hz].
  + apply (chunk_ok_val SEGS _ _ (spZ regs - 128) 16 8 (SOff 46 0) seen);
    [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hs].
- change (rm_Es regsL (rm_xsN z2 seen ty kids n)) with E. constructor; [|constructor].
  unfold region_ok, rm_nodereg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  assert (B9 : base_val E (Some 9%nat) = z1) by (cbn [base_val]; exact U9).
  rewrite B9. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
  constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (chunk_ok_val SEGS E _ z1 0 4 tv ty); [exact Htv | cbn; lia | lia | rewrite Z.add_0_r; exact Hty].
  + apply (chunk_ok_val SEGS E _ z1 24 8 (SOff 49 0) kids);
    [cbn [sv_denot]; rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hk].
  + apply (chunk_ok_val SEGS E _ z1 40 8 (SOff 50 0) n);
    [cbn [sv_denot]; rewrite E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hn].
- change (rm_Es regsL (rm_xsN z2 seen ty kids n)) with E.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, rm_frame_region, rm_nodereg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U9. repeat split; try exact I; lia.
- change (rm_Es regsL (rm_xsN z2 seen ty kids n)) with E.
  split; [|split; [exact I | exact I]]. cbn [rm_factsN f_atoms atoms_ok].
  split; [apply (rm_afact E 2 (spZ regs - 128)); [exact U2 | lia | change (2 ^ 4) with 16; lia | lia]|].
  split; [apply (rm_afact E 9 z1); [exact U9 | lia | change (2 ^ 3) with 8; lia | lia]|].
  split; [apply (rm_afact E nB SHADOW_OFF); [exact HB | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  exact I.
Qed.

(* the loop head's register map: the node's count and kids words' addresses, the three shadow cells (base atom 47),
   the array tag *)
Definition rm_srP : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18%bv (SOff 9 24)) 19%bv (SOff 9 40)) 20%bv (rm_shxc 47 9 24))
    22%bv (rm_shxc 47 9 0)) 23%bv (SLit 5)) 27%bv (rm_shxc 47 9 40).
(* the arithmetic of a refuted UBSan trap branch: drop each zcanon whose argument is in range, then split each test *)
Ltac rm_zc H :=
  repeat match type of H with context [zcanon ?x] =>
    rewrite (zcanon_id x) in H by (unfold M64; repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia)
  end.
Ltac rm_ltb H := repeat match type of H with context [?a <? ?b] => destruct (Z.ltb_spec a b) end.
(* a register kept by a stretch: the same expression in the state after it as in the seat, over an env that extends
   the seat's *)
Lemma rm_regs_carry : forall E E' sr (regsL : bvmap 5 word) ss ms (H : word -> bool) (rl : list (bv 5)) (kk : nat),
  regs_ok E sr regsL -> st_ok_pi SEGS VAL E' ss (restrict H ms) -> env_agree kk E E' ->
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) r) (sr_get sr r) && sv_atoms_lt kk (sr_get sr r)) rl = true ->
  forall r, In r rl -> getr (ms_regs ms) r = getr regsL r.
Proof.
intros E E' sr regsL ss ms H rl kk HR HS HA Hall r Hr.
rewrite (st_ok_pi_restrict_reg H E' ss ms r HS).
rewrite forallb_forall in Hall. specialize (Hall r Hr). apply andb_prop in Hall as [Heq Hlt].
apply sv_eqb_eq in Heq. rewrite Heq, (sv_denot_agree kk E E' _ HA Hlt). symmetry. exact (HR r).
Qed.
Lemma rm_regs_carry_ok : forall E E' sr (regsL : bvmap 5 word) ss ms (H : word -> bool) (rl : list (bv 5)) (kk : nat),
  regs_ok E sr regsL -> st_ok SEGS E' ss (restrict H ms) -> env_agree kk E E' ->
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) r) (sr_get sr r) && sv_atoms_lt kk (sr_get sr r)) rl = true ->
  forall r, In r rl -> getr (ms_regs ms) r = getr regsL r.
Proof.
intros E E' sr regsL ss ms H rl kk HR HS HA Hall r Hr.
rewrite (st_ok_restrict_reg SEGS H E' ss ms r HS).
rewrite forallb_forall in Hall. specialize (Hall r Hr). apply andb_prop in Hall as [Heq Hlt].
apply sv_eqb_eq in Heq. rewrite Heq, (sv_denot_agree kk E E' _ HA Hlt). symmetry. exact (HR r).
Qed.
(* the params seat at any pc from rm_parst *)
Lemma rm_par_seat : forall pc j W2 regsL mem2 md2 ly2 k z1 z2 seen items D1 kids,
  rm_parst j W2 regsL mem2 md2 ly2 k z1 z2 seen items D1 kids ->
  regs_ok (rm_Es regsL (rm_xsN z2 seen 5 kids (Z.of_nat (length items)))) rm_srP regsL /\
  st_ok_pi SEGS VAL (rm_Es regsL (rm_xsN z2 seen 5 kids (Z.of_nat (length items))))
    (mkSS pc rm_srP [rm_frame_region rm_chT; rm_nodereg (SLit 5)] None (rm_factsN 47))
    (restrict (w_H W2) (mkst regsL (Z_to_bv 64 (BASE + pc)) mem2 (seg_rom SEGS))).
Proof.
intros pc j W2 regsL mem2 md2 ly2 k z1 z2 seen items D1 kids
  (HI & Hseen & Hseen0 & Hz2v & Hz2s & Rz2 & Hs1 & Hk & Hj & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23
   & G24 & G25 & G27).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _]. pose proof (@YM05.alloc_ceiling_lt rc) as CLT.
pose proof HI as ((HJ & Eab) & _).
destruct (rm_arr_info z1 items D1 Hs1) as (kids0 & cap0 & Hk0e & Hn0e & Hty0e & Hal0 & Hcn0 & Hcap0).
assert (Ek : kids0 = kids) by exact (rm_val8_uniq _ _ _ _ (proj2 Hk0e) (proj2 Hk) (proj1 Hk0e) (proj1 Hk)).
subst kids0.
pose proof (rm_sub_range z1 _ D1 Hs1) as (Z1lo & Z1hi).
set (nn := Z.of_nat (length items)) in *.
assert (Htyc : rd_u32 SEGS (rdW W2 mem2) z1 5)
  by (split; [lia | apply (rm_sub_val z1 _ D1 ly2 W2 mem2 md2 k z1 4 5 Hs1 (conj HJ Eab)); [lia | cbn; lia | exact (proj2 Hty0e)]]).
assert (Hkc : rd_u64 SEGS (rdW W2 mem2) (z1 + 24) kids)
  by (split; [exact (proj1 Hk) | apply (rm_sub_val z1 _ D1 ly2 W2 mem2 md2 k (z1 + 24) 8 kids Hs1 (conj HJ Eab));
      [lia | cbn; lia | exact (proj2 Hk)]]).
assert (Hnc : rd_u64 SEGS (rdW W2 mem2) (z1 + 40) nn)
  by (split; [exact (proj1 Hn0e) | apply (rm_sub_val z1 _ D1 ly2 W2 mem2 md2 k (z1 + 40) 8 nn Hs1 (conj HJ Eab));
      [lia | cbn; lia | exact (proj2 Hn0e)]]).
set (E := rm_Es regsL (rm_xsN z2 seen 5 kids nn)).
assert (ER : forall n' (r : bv 5), (n' < 32)%nat -> Z.of_nat n' = bv_unsigned r -> ew E n' = getr regsL r)
  by (intros n' r Hn' Hr; exact (rm_Es_reg regsL (rm_xsN z2 seen 5 kids nn) n' r Hn' Hr)).
assert (E47 : ew E 47 = Z_to_bv 64 SHADOW_OFF) by exact (rm_Es_x regsL (rm_xsN z2 seen 5 kids nn) 2 ltac:(cbn; lia) ltac:(lia)).
assert (UB47 : bv_unsigned (ew E 47) = SHADOW_OFF) by (rewrite E47; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E 9) = z1)
  by (rewrite (ER 9%nat 9%bv), G9 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; lia).
assert (HR : regs_ok E rm_srP regsL).
{ unfold rm_srP. repeat apply rm_regs_ok_set.
  all: lazymatch goal with
  | |- regs_ok _ sr_atoms _ => subst E; unfold rm_Es; apply regs_ok_Eimg_Ereg
  | |- getr _ _ = sv_denot _ (SOff 9 ?c) =>
      apply (rm_reg_U E _ _ (z1 + c)); [first [exact G18 | exact G19] | lia | rewrite U_SOff, U9; unfold zcanon, M64; apply Z.mod_small; lia]
  | |- getr _ _ = sv_denot _ (rm_shxc 47 9 ?c) =>
      apply (rm_reg_U E _ _ (SHADOW_OFF + (z1 + c) / 8));
      [ first [exact G20 | exact G27 | rewrite Z.add_0_r; exact G22]
      | pose proof (Z.div_pos (z1 + c) 8 ltac:(lia) ltac:(lia)); assert ((z1 + c) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia);
        unfold SHADOW_OFF; lia
      | apply rm_shxc_U; [exact UB47 | rewrite U9; reflexivity | lia] ]
  | |- getr _ _ = sv_denot _ (SLit 5) => rewrite G23; reflexivity
  end. }
split; [exact HR|].
exact (rm_seatN regsL W2 mem2 ly2 md2 k pc z2 seen z1 5 kids nn (SLit 5) rm_srP 47
  HI Hseen Hseen0 Hz2v Rz2 G2 G9 Z1lo ltac:(lia) Hal0 Htyc Hkc Hnc eq_refl HR UB47).
Qed.
(* the back edge (slot 122): the counter, the shadow of the node's type word, the type word (5), j + 1, the loop head *)
Lemma rm_par_back : forall n, ((0 < n)%nat -> rm_parP (n - 1)) ->
  forall j W2 regsL mem2 md2 ly2 k z1 z2 seen items D1 kids,
  (length items - j = n)%nat -> (j < length items)%nat -> rm_parst j W2 regsL mem2 md2 ly2 k z1 z2 seen items D1 kids ->
  SRr SEGS W2 (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_rmB + 488))) mem2 (seg_rom SEGS)) md2) rm_goal.
Proof.
intros n IH j W2 regsL mem2 md2 ly2 k z1 z2 seen items D1 kids Hlen Hjl
  (HI & Hseen & Hseen0 & Hz2v & Hz2s & Rz2 & Hs1 & Hk & Hj & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23
   & G24 & G25 & G27).
pose proof rm_stks as (FS & FS1 & FS2). pose proof rm_sp_bounds as (SB1 & SB2 & SB3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _]. pose proof (@YM05.alloc_ceiling_lt rc) as CLT.
pose proof HI as ((HJ & Eab) & HLd & HPM & HFR).
destruct (rm_arr_info z1 items D1 Hs1) as (kids0 & cap0 & Hk0e & Hn0e & Hty0e & Hal0 & Hcn0 & Hcap0).
assert (Ek : kids0 = kids) by exact (rm_val8_uniq _ _ _ _ (proj2 Hk0e) (proj2 Hk) (proj1 Hk0e) (proj1 Hk)).
subst kids0.
pose proof (rm_sub_range z1 _ D1 Hs1) as (Z1lo & Z1hi).
set (nn := Z.of_nat (length items)) in *.
assert (Htyc : rd_u32 SEGS (rdW W2 mem2) z1 5)
  by (split; [lia | apply (rm_sub_val z1 _ D1 ly2 W2 mem2 md2 k z1 4 5 Hs1 (conj HJ Eab)); [lia | cbn; lia | exact (proj2 Hty0e)]]).
assert (Hkc : rd_u64 SEGS (rdW W2 mem2) (z1 + 24) kids)
  by (split; [exact (proj1 Hk) | apply (rm_sub_val z1 _ D1 ly2 W2 mem2 md2 k (z1 + 24) 8 kids Hs1 (conj HJ Eab));
      [lia | cbn; lia | exact (proj2 Hk)]]).
assert (Hnc : rd_u64 SEGS (rdW W2 mem2) (z1 + 40) nn)
  by (split; [exact (proj1 Hn0e) | apply (rm_sub_val z1 _ D1 ly2 W2 mem2 md2 k (z1 + 40) 8 nn Hs1 (conj HJ Eab));
      [lia | cbn; lia | exact (proj2 Hn0e)]]).
set (E := rm_Es regsL (rm_xsN z2 seen 5 kids nn)).
assert (ER : forall n' (r : bv 5), (n' < 32)%nat -> Z.of_nat n' = bv_unsigned r -> ew E n' = getr regsL r)
  by (intros n' r Hn' Hr; exact (rm_Es_reg regsL (rm_xsN z2 seen 5 kids nn) n' r Hn' Hr)).
assert (E47 : ew E 47 = Z_to_bv 64 SHADOW_OFF) by exact (rm_Es_x regsL (rm_xsN z2 seen 5 kids nn) 2 ltac:(cbn; lia) ltac:(lia)).
assert (UB47 : bv_unsigned (ew E 47) = SHADOW_OFF) by (rewrite E47; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 128)
  by (rewrite (ER 2%nat 2%bv), G2 by (lia || reflexivity); apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = z1)
  by (rewrite (ER 9%nat 9%bv), G9 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; lia).
assert (HR : regs_ok E rm_srP regsL).
{ unfold rm_srP. repeat apply rm_regs_ok_set.
  all: lazymatch goal with
  | |- regs_ok _ sr_atoms _ => subst E; unfold rm_Es; apply regs_ok_Eimg_Ereg
  | |- getr _ _ = sv_denot _ (SOff 9 ?c) =>
      apply (rm_reg_U E _ _ (z1 + c)); [first [exact G18 | exact G19] | lia | rewrite U_SOff, U9; unfold zcanon, M64; apply Z.mod_small; lia]
  | |- getr _ _ = sv_denot _ (rm_shxc 47 9 ?c) =>
      apply (rm_reg_U E _ _ (SHADOW_OFF + (z1 + c) / 8));
      [ first [exact G20 | exact G27 | rewrite Z.add_0_r; exact G22]
      | pose proof (Z.div_pos (z1 + c) 8 ltac:(lia) ltac:(lia)); assert ((z1 + c) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia);
        unfold SHADOW_OFF; lia
      | apply rm_shxc_U; [exact UB47 | rewrite U9; reflexivity | lia] ]
  | |- getr _ _ = sv_denot _ (SLit 5) => rewrite G23; reflexivity
  end. }
pose proof (rm_seatN regsL W2 mem2 ly2 md2 k (AF_rmB + 488) z2 seen z1 5 kids nn (SLit 5) rm_srP 47
  HI Hseen Hseen0 Hz2v Rz2 G2 G9 Z1lo ltac:(lia) Hal0 Htyc Hkc Hnc eq_refl HR UB47) as HS.
change (rm_Es regsL (rm_xsN z2 seen 5 kids nn)) with E in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rm_Es; apply Eimg_env).
assert (E45 : ew E 45 = Z_to_bv 64 z2) by exact (rm_Es_x regsL (rm_xsN z2 seen 5 kids nn) 0 ltac:(cbn; lia) ltac:(lia)).
assert (SHOK : sh_ok SEGS (SOff 47 0) [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (Hsp : spZ regsL = spZ regs - 128) by (unfold spZ at 1; rewrite G2; apply unsigned_lit_small; lia).
pose proof (rm_sub_rslot_now z1 _ D1 ly2 W2 mem2 md2 k regsL 0 Hs1 (conj HJ Eab) Hsp ltac:(lia)) as (_ & _ & _ & _ & HRA1 & _).
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_rm_B PA B PST ARx _ LAWS _ RLAW).
(* ---- slots 122 .. 130 to the head ---- *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM RM_Bspan (AF_rmB + 336).
all: try (rm_awr U2).
all: try (lazymatch goal with |- range_addressable _ _ _ _ =>
  cbn [ms_mem mkst]; rewrite !U_SOff, UB47, U9, !Z.add_0_r; unfold zcanon, M64;
  rewrite !Z.mod_small by (unfold SHADOW_OFF; lia);
  change (rd_of SEGS (rdW W2 mem2)) with (aview SEGS (w_H W2) mem2);
  eapply range_addressable_sub; [exact HRA1 | lia | lia] end).
clear HG.
rm_reinv HI HS HJ HPM HFr U2 HI1. clear HF HFr.
pose proof (rm_regs_carry E _ rm_srP regsL _ _ _ [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 27%bv]
  512 HR HS ltac:(split; [intros n' Hn'; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity])
  ltac:(vm_compute; reflexivity)) as KC.
rm_rawreg HS (24%bv : bv 5) N24. rm_rawreg HS (25%bv : bv 5) N25.
assert (EW24 : ew E 24 = w64 (56 * Z.of_nat j)) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact G24).
assert (EW25 : ew E 25 = w64 (Z.of_nat j)) by (rewrite (ER 25%nat 25%bv) by (lia || reflexivity); exact G25).
rm_frame_rg HS RG1.
lazymatch type of RG1 with region_ok _ ?E1 _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
  pose proof (rm_slot_of_region E1 _ _ 8 (SOff 45 0) RG1 ltac:(rewrite ?ew_ewset_other by lia; exact U2)
    ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hz21;
  lazymatch cs with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
    pose proof (rm_slot_of_region E1 _ _ 16 e16 RG1 ltac:(rewrite ?ew_ewset_other by lia; exact U2)
      ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hseen1;
    set (seen1 := bv_unsigned (sv_denot E1 e16)) in Hseen1 end end.
clear RG1.
rewrite rm_sv0, ?ew_ewset_other, E45, unsigned_lit_small in Hz21 by lia.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into ms1 end.
pmkst HS.
eapply (IH ltac:(lia) (Datatypes.S j) W2 (ms_regs ms1) (ms_mem ms1) _ _ _ z1 z2 seen1 items D1 kids ltac:(lia)).
split; [exact HI1|]. split; [exact Hseen1|]. split; [apply bv_unsigned_in_range|].
split; [exact Hz21|]. split; [exact Hz2s|]. split; [exact Rz2|]. split; [exact Hs1|]. split; [exact Hk|].
split; [lia|].
split; [rewrite (KC 2%bv) by (cbn; tauto); exact G2|].
split; [rewrite (KC 3%bv) by (cbn; tauto); exact G3|].
split; [rewrite (KC 4%bv) by (cbn; tauto); exact G4|].
split; [rewrite (KC 8%bv) by (cbn; tauto); exact G8|].
split; [rewrite (KC 9%bv) by (cbn; tauto); exact G9|].
split; [rewrite (KC 18%bv) by (cbn; tauto); exact G18|].
split; [rewrite (KC 19%bv) by (cbn; tauto); exact G19|].
split; [rewrite (KC 20%bv) by (cbn; tauto); exact G20|].
split; [rewrite (KC 21%bv) by (cbn; tauto); exact G21|].
split; [rewrite (KC 22%bv) by (cbn; tauto); exact G22|].
split; [rewrite (KC 23%bv) by (cbn; tauto); exact G23|].
split; [rewrite N24, (rm_w64_off _ 24 (56 * Z.of_nat j) _) by (rewrite ?ew_ewset_other by lia; exact EW24); f_equal; lia|].
split; [rewrite N25, (rm_w64_off _ 25 (Z.of_nat j) _) by (rewrite ?ew_ewset_other by lia; exact EW25); f_equal; lia|].
rewrite (KC 27%bv) by (cbn; tauto); exact G27.
Qed.
Lemma rm_par_iter : forall n, ((0 < n)%nat -> rm_parP (n - 1)) -> rm_parP n.
Proof.
intros n IH j W2 regsL mem2 md2 ly2 k z1 z2 seen items D1 kids Hlen
  (HI & Hseen & Hseen0 & Hz2v & Hz2s & Rz2 & Hs1 & Hk & Hj & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23
   & G24 & G25 & G27).
pose proof rm_stks as (FS & FS1 & FS2). pose proof rm_sp_bounds as (SB1 & SB2 & SB3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _]. pose proof (@YM05.alloc_ceiling_lt rc) as CLT.
pose proof HI as ((HJ & Eab) & HLd & HPM & HFR).
destruct (rm_arr_info z1 items D1 Hs1) as (kids0 & cap0 & Hk0e & Hn0e & Hty0e & Hal0 & Hcn0 & Hcap0).
assert (Ek : kids0 = kids) by exact (rm_val8_uniq _ _ _ _ (proj2 Hk0e) (proj2 Hk) (proj1 Hk0e) (proj1 Hk)).
subst kids0.
pose proof (rm_sub_range z1 _ D1 Hs1) as (Z1lo & Z1hi).
set (nn := Z.of_nat (length items)) in *.
assert (Htyc : rd_u32 SEGS (rdW W2 mem2) z1 5)
  by (split; [lia | apply (rm_sub_val z1 _ D1 ly2 W2 mem2 md2 k z1 4 5 Hs1 (conj HJ Eab)); [lia | cbn; lia | exact (proj2 Hty0e)]]).
assert (Hkc : rd_u64 SEGS (rdW W2 mem2) (z1 + 24) kids)
  by (split; [exact (proj1 Hk) | apply (rm_sub_val z1 _ D1 ly2 W2 mem2 md2 k (z1 + 24) 8 kids Hs1 (conj HJ Eab));
      [lia | cbn; lia | exact (proj2 Hk)]]).
assert (Hnc : rd_u64 SEGS (rdW W2 mem2) (z1 + 40) nn)
  by (split; [exact (proj1 Hn0e) | apply (rm_sub_val z1 _ D1 ly2 W2 mem2 md2 k (z1 + 40) 8 nn Hs1 (conj HJ Eab));
      [lia | cbn; lia | exact (proj2 Hn0e)]]).
set (E := rm_Es regsL (rm_xsN z2 seen 5 kids nn)).
assert (ER : forall n' (r : bv 5), (n' < 32)%nat -> Z.of_nat n' = bv_unsigned r -> ew E n' = getr regsL r)
  by (intros n' r Hn' Hr; exact (rm_Es_reg regsL (rm_xsN z2 seen 5 kids nn) n' r Hn' Hr)).
assert (E47 : ew E 47 = Z_to_bv 64 SHADOW_OFF) by exact (rm_Es_x regsL (rm_xsN z2 seen 5 kids nn) 2 ltac:(cbn; lia) ltac:(lia)).
assert (E49 : ew E 49 = Z_to_bv 64 kids) by exact (rm_Es_x regsL (rm_xsN z2 seen 5 kids nn) 4 ltac:(cbn; lia) ltac:(lia)).
assert (E50 : ew E 50 = Z_to_bv 64 nn) by exact (rm_Es_x regsL (rm_xsN z2 seen 5 kids nn) 5 ltac:(cbn; lia) ltac:(lia)).
assert (UB47 : bv_unsigned (ew E 47) = SHADOW_OFF) by (rewrite E47; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 128)
  by (rewrite (ER 2%nat 2%bv), G2 by (lia || reflexivity); apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = z1)
  by (rewrite (ER 9%nat 9%bv), G9 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = Z.of_nat j).
{ rewrite (ER 25%nat 25%bv), G25 by (lia || reflexivity). unfold w64. apply unsigned_lit_small.
  pose proof (rm_arr_info z1 items D1 Hs1). destruct Hcap0 as [(Hc0 & _) | (Hc0 & Hk1 & Hk2)]; lia. }
assert (U49 : bv_unsigned (ew E 49) = kids) by (rewrite E49; apply unsigned_lit_small; exact (proj1 Hk)).
assert (U50 : bv_unsigned (ew E 50) = nn) by (rewrite E50; apply unsigned_lit_small; exact (proj1 Hn0e)).
assert (HR : regs_ok E rm_srP regsL).
{ unfold rm_srP. repeat apply rm_regs_ok_set.
  all: lazymatch goal with
  | |- regs_ok _ sr_atoms _ => subst E; unfold rm_Es; apply regs_ok_Eimg_Ereg
  | |- getr _ _ = sv_denot _ (SOff 9 ?c) =>
      apply (rm_reg_U E _ _ (z1 + c)); [first [exact G18 | exact G19] | lia | rewrite U_SOff, U9; unfold zcanon, M64; apply Z.mod_small; lia]
  | |- getr _ _ = sv_denot _ (rm_shxc 47 9 ?c) =>
      apply (rm_reg_U E _ _ (SHADOW_OFF + (z1 + c) / 8));
      [ first [exact G20 | exact G27 | rewrite Z.add_0_r; exact G22]
      | pose proof (Z.div_pos (z1 + c) 8 ltac:(lia) ltac:(lia)); assert ((z1 + c) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia);
        unfold SHADOW_OFF; lia
      | apply rm_shxc_U; [exact UB47 | rewrite U9; reflexivity | lia] ]
  | |- getr _ _ = sv_denot _ (SLit 5) => rewrite G23; reflexivity
  end. }
pose proof (rm_seatN regsL W2 mem2 ly2 md2 k (AF_rmB + 336) z2 seen z1 5 kids nn (SLit 5) rm_srP 47
  HI Hseen Hseen0 Hz2v Rz2 G2 G9 Z1lo ltac:(lia) Hal0 Htyc Hkc Hnc eq_refl HR UB47) as HS.
change (rm_Es regsL (rm_xsN z2 seen 5 kids nn)) with E in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rm_Es; apply Eimg_env).
assert (E45 : ew E 45 = Z_to_bv 64 z2) by exact (rm_Es_x regsL (rm_xsN z2 seen 5 kids nn) 0 ltac:(cbn; lia) ltac:(lia)).
assert (HAE : env_agree 32 (Ereg regsL (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) (rm_xsN z2 seen 5 kids nn))) E)
  by (split; [intros n' Hn'; subst E; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS (SOff 47 0) [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (Hsp : spZ regsL = spZ regs - 128) by (unfold spZ at 1; rewrite G2; apply unsigned_lit_small; lia).
pose proof (rm_sub_rslot_now z1 _ D1 ly2 W2 mem2 md2 k regsL 0 Hs1 (conj HJ Eab) Hsp ltac:(lia)) as (_ & _ & _ & _ & HRA1 & _).
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_rm_B PA B PST ARx _ LAWS _ RLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_rm_B PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
(* ---- slots 84 .. 87: the shadow of the count word (an obligation), the count, bgeu j count ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_Bspan.
all: try (rm_awr U2).
all: try (lazymatch goal with |- range_addressable _ _ _ _ =>
  cbn [ms_mem mkst]; rewrite !U_SOff, UB47, U9, !Z.add_0_r; unfold zcanon, M64;
  rewrite !Z.mod_small by (unfold SHADOW_OFF; lia);
  change (rd_of SEGS (rdW W2 mem2)) with (aview SEGS (w_H W2) mem2);
  eapply range_addressable_sub; [exact HRA1 | lia | lia] end).
clear HG.
rm_reinv HI HS HJ HPM HFr U2 HI1. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK RM_Bspan.
all: rewrite branch_geu_U, !U_SOff in Hc; rewrite ?ew_ewset_other in Hc by lia; rewrite U25, U50, !Z.add_0_r in Hc;
  rm_zc Hc.
- (* taken: j >= count; to the tail *)
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM RM_Bspan (AF_rmB + 544); [rm_awr U2|].
  clear HG.
  rm_reinv HI1 HS HJ HPM HFr U2 HI2. clear HF HFr.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) _ _ _ regsL _ [2%bv; 3%bv; 4%bv] HS
    ltac:(eapply env_agree_trans; [exact HAE | split; [intros n' Hn'; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]])
    ltac:(vm_compute; reflexivity)) as K2.
  rm_frame_rg HS RG2.
  lazymatch type of RG2 with region_ok _ ?E2 _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
    pose proof (rm_slot_of_region E2 _ _ 8 (SOff 45 0) RG2 ltac:(rewrite ?ew_ewset_other by lia; exact U2)
      ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hz22;
    lazymatch cs with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
      pose proof (rm_slot_of_region E2 _ _ 16 e16 RG2 ltac:(rewrite ?ew_ewset_other by lia; exact U2)
        ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hseen2;
      set (seen2 := bv_unsigned (sv_denot E2 e16)) in Hseen2 end end.
  clear RG2.
  rewrite rm_sv0, ?ew_ewset_other, E45, unsigned_lit_small in Hz22 by lia.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into ms2 end.
  pmkst HS.
  eapply (rm_tail W2 (ms_regs ms2) (ms_mem ms2) _ _ _ z2 seen2).
  split; [exact HI2|]. split; [exact Hseen2|]. split; [apply bv_unsigned_in_range|]. split; [exact Hz22|].
  split; [rewrite (K2 2%bv) by (cbn; tauto); exact G2|].
  split; [rewrite (K2 3%bv) by (cbn; tauto); exact G3|].
  split; [rewrite (K2 4%bv) by (cbn; tauto); exact G4|].
  split; [exact Hz2s | exact Rz2].
- (* not taken: j < count; item j: the shadow of the kids word, the kids word, the UBSan traps on kids + 56 j *)
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hcap : 0 < cap0 /\ 4096 <= kids /\ kids + 56 * cap0 <= YM05.alloc_ceiling)
    by (destruct Hcap0 as [(Hc0 & _) | Hc1]; [lia | exact Hc1]).
  destruct Hcap as (Hcp & Hk4 & Hkc2).
  pose proof (rm_sub_rslot_now z1 _ D1 _ _ _ _ _ regsL 0 Hs1 (proj1 HI1) Hsp ltac:(lia)) as (_ & _ & _ & _ & HRA2 & _).
  paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_Bspan.
  all: try (rm_awr U2).
  all: try (lazymatch goal with |- range_addressable _ _ _ _ =>
    cbn [ms_mem mkst]; rewrite !U_SOff, ?ew_ewset_other by lia; rewrite UB47, U9, !Z.add_0_r; unfold zcanon, M64;
    rewrite !Z.mod_small by (unfold SHADOW_OFF; lia);
    lazymatch goal with |- range_addressable (rd_of ?sg (mrestrict ?H ?m)) _ _ _ =>
      change (rd_of sg (mrestrict H m)) with (aview sg H m) end;
    eapply range_addressable_sub; [exact HRA2 | lia | lia] end).
  clear HG.
  rm_reinv HI1 HS HJ HPM HFr U2 HI2. clear HF HFr.
  assert (Hjc : Z.of_nat j < cap0) by lia.
  (* slot 97: beq (kids <> 0) (kids + 56 j = 0), the null-pointer trap: refuted, kids >= 4096 *)
  rename Hc into Hjn.
  psrr_branch_tok RUN BR HS SHOK RM_Bspan.
  { exfalso. rewrite branch_eq_U in Hc.
    repeat first [rewrite U_SAlu in Hc | rewrite U_SMd in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
    cbn [zalu_raw zmd_raw] in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite U25, U49, ?Z.add_0_r in Hc.
    rm_zc Hc. rm_ltb Hc; cbn in Hc; try discriminate Hc; lia. }
  clear Hc. paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_Bspan; [rm_awr U2|].
  clear HG.
  rm_reinv HI2 HS HJ HPM HFr U2 HI3. clear HF HFr.
  (* slot 98: bltu (kids + 56 j) kids, the pointer-overflow trap: refuted *)
  psrr_branch_tok RUN BR HS SHOK RM_Bspan.
  { exfalso. rewrite branch_ltu_U in Hc.
    repeat first [rewrite U_SAlu in Hc | rewrite U_SMd in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
    cbn [zalu_raw zmd_raw] in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite U25, U49, ?Z.add_0_r in Hc.
    rm_zc Hc. rm_ltb Hc; cbn in Hc; try discriminate Hc; lia. }
  clear Hc. paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_Bspan; [rm_awr U2|].
  clear HG.
  rm_reinv HI3 HS HJ HPM HFr U2 HI4. clear HF HFr.
  (* slot 104: bnez (mulh j 56 <> sra (56 j) 63), the multiply-overflow trap: refuted *)
  psrr_branch_tok RUN BR HS SHOK RM_Bspan.
  { exfalso. rewrite branch_ne_U in Hc.
    repeat first [rewrite U_SAlu in Hc | rewrite U_SMd in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
    cbn [zalu_raw zmd_raw] in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite U25, ?Z.add_0_r in Hc.
    rm_zc Hc.
    rewrite ?(swrap64_id (Z.of_nat j)), ?(swrap64_id 56), ?(swrap64_id (Z.of_nat j * 56)) in Hc by (unfold half64; lia).
    change (Z.of_N 64) with 64 in Hc. change (Z.land 63 63) with 63 in Hc.
    rewrite !Z.shiftr_div_pow2 in Hc by lia.
    rewrite (Z.div_small (Z.of_nat j * 56) (2 ^ 63)), (Z.div_small (Z.of_nat j * 56) (2 ^ 64)) in Hc by lia.
    cbn in Hc. discriminate Hc. }
  (* slots 105 .. 107: a0 = kids + 56 j, a1 = "symbol", the call pj_get_str (item j, "symbol") *)
  clear Hc. paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_Bspan; [rm_awr U2|].
  clear HG.
  rm_reinv HI4 HS HJ HPM HFr U2 HI5. clear HF HFr.
  pose proof (rm_regs_carry_ok E _ rm_srP regsL _ _ _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 27%bv]
    512 HR HS ltac:(split; [intros n' Hn'; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity])
    ltac:(vm_compute; reflexivity)) as KC5.
  prreg HS (1%bv : bv 5) R1. rm_rawreg HS (10%bv : bv 5) N10. rm_rawreg HS (11%bv : bv 5) N11.
  rm_rawreg HS (26%bv : bv 5) N26.
  rm_frame_rg HS RG5.
  lazymatch type of RG5 with region_ok _ ?E5 _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
    pose proof (rm_slot_of_region E5 _ _ 8 (SOff 45 0) RG5 ltac:(rewrite ?ew_ewset_other by lia; exact U2)
      ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hz25;
    lazymatch cs with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
      pose proof (rm_slot_of_region E5 _ _ 16 e16 RG5 ltac:(rewrite ?ew_ewset_other by lia; exact U2)
        ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hseen5;
      set (seen5 := bv_unsigned (sv_denot E5 e16)) in Hseen5 end end.
  clear RG5.
  rewrite rm_sv0, ?ew_ewset_other, E45, unsigned_lit_small in Hz25 by lia.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msq) => rename msq into ms5 end.
  assert (Hsp5 : spZ (ms_regs ms5) = spZ regs - 128)
    by (unfold spZ at 1; rewrite (KC5 2%bv) by (cbn; tauto); rewrite G2; apply unsigned_lit_small; lia).
  destruct (nth_error items j) as [u|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
  destruct (rm_item_sub z1 items D1 j u Hs1 Hnth) as (kids1 & Du & Hk1 & Hsu).
  assert (Ek1 : kids1 = kids) by exact (rm_val8_uniq _ _ _ _ (proj2 Hk1) (proj2 Hk) (proj1 Hk1) (proj1 Hk)).
  subst kids1.
  assert (U24 : bv_unsigned (ew E 24) = 56 * Z.of_nat j)
    by (rewrite (ER 24%nat 24%bv), G24 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; lia).
  pose proof rm_pa_o2 as Ho2. unfold IMG_LO_B in Ho2. pose proof (pa_val_range (A_OBJ 2)) as RV2.
  (* ---- the call pj_get_str (item j, "symbol") (slot 107) ---- *)
  eapply SRr_bind.
  { eapply (rm_call_inv true W2 _ _ ms5 ly2 _ _ (kids + 56 * Z.of_nat j) 0x11140 [115; 121; 109; 98; 111; 108] u Du
      (AF_rmB + 432) HS eq_refl eq_refl HI5 Hsp5).
    - rewrite (KC5 3%bv) by (cbn; tauto). exact G3.
    - rewrite (KC5 4%bv) by (cbn; tauto). exact G4.
    - exact R1.
    - unfold AF_rmB, RMB_SLOT. lia.
    - unfold AF_rmB, RMB_SLOT. reflexivity.
    - vm_compute. reflexivity.
    - left. unfold s0Z. rewrite (KC5 8%bv) by (cbn; tauto). rewrite G8. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - apply (rm_U_reg _ _ _ _ N10); [|lia].
      rewrite U_SAlu, !U_SOff, ?ew_ewset_other by lia. rewrite U24, U49, !Z.add_0_r. cbn [zalu_raw]. unfold zcanon, M64.
      rewrite !Z.mod_small by lia. lia.
    - rewrite N11, rm_sv0, ?ew_ewset_other by lia. rewrite (ER 8%nat 8%bv), G8 by (lia || reflexivity). try (f_equal; lia).
    - cbn [rm_keytab In]. repeat first [left; reflexivity | right].
    - right; right. exact Hsu. }
  cbv beta. intros W3 c3 _ (ly3 & regs3 & mem3 & md3 & k3 & -> & HI6 & HP6 & HKF6 & _).
  rewrite R1.
  rm_pres HP6 2 (2%bv : bv 5) Q2. rm_pres HP6 3 (3%bv : bv 5) Q3. rm_pres HP6 4 (4%bv : bv 5) Q4.
  rm_pres HP6 8 (8%bv : bv 5) Q8. rm_pres HP6 9 (9%bv : bv 5) Q9. rm_pres HP6 18 (18%bv : bv 5) Q18.
  rm_pres HP6 19 (19%bv : bv 5) Q19. rm_pres HP6 20 (20%bv : bv 5) Q20. rm_pres HP6 21 (21%bv : bv 5) Q21.
  rm_pres HP6 22 (22%bv : bv 5) Q22. rm_pres HP6 23 (23%bv : bv 5) Q23. rm_pres HP6 24 (24%bv : bv 5) Q24.
  rm_pres HP6 25 (25%bv : bv 5) Q25. rm_pres HP6 26 (26%bv : bv 5) Q26. rm_pres HP6 27 (27%bv : bv 5) Q27.
  assert (HP3st : rm_parst j W3 regs3 mem3 md3 ly3 k3 z1 z2 seen5 items D1 kids).
  { split; [exact HI6|]. split; [apply HKF6; [lia | cbn; lia | exact Hseen5]|]. split; [apply bv_unsigned_in_range|].
    split; [apply HKF6; [lia | cbn; lia | exact Hz25]|]. split; [exact Hz2s|]. split; [exact Rz2|]. split; [exact Hs1|].
    split; [exact Hk|]. split; [lia|].
    split; [rewrite Q2, (KC5 2%bv) by (cbn; tauto); exact G2|].
    split; [rewrite Q3, (KC5 3%bv) by (cbn; tauto); exact G3|].
    split; [rewrite Q4, (KC5 4%bv) by (cbn; tauto); exact G4|].
    split; [rewrite Q8, (KC5 8%bv) by (cbn; tauto); exact G8|].
    split; [rewrite Q9, (KC5 9%bv) by (cbn; tauto); exact G9|].
    split; [rewrite Q18, (KC5 18%bv) by (cbn; tauto); exact G18|].
    split; [rewrite Q19, (KC5 19%bv) by (cbn; tauto); exact G19|].
    split; [rewrite Q20, (KC5 20%bv) by (cbn; tauto); exact G20|].
    split; [rewrite Q21, (KC5 21%bv) by (cbn; tauto); exact G21|].
    split; [rewrite Q22, (KC5 22%bv) by (cbn; tauto); exact G22|].
    split; [rewrite Q23, (KC5 23%bv) by (cbn; tauto); exact G23|].
    split; [rewrite Q24, (KC5 24%bv) by (cbn; tauto); exact G24|].
    split; [rewrite Q25, (KC5 25%bv) by (cbn; tauto); exact G25|].
    rewrite Q27, (KC5 27%bv) by (cbn; tauto); exact G27. }
  assert (G3_26 : getr regs3 26 = w64 (56 * Z.of_nat j)).
  { rewrite Q26. apply (rm_U_reg _ _ _ _ N26); [|lia].
    rewrite U_SMd, U_SOff, U_SLit, ?ew_ewset_other by lia. rewrite U25, Z.add_0_r. cbn [zmd_raw].
    rewrite (zcanon_id (Z.of_nat j)), (zcanon_id 56) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
  destruct (rm_par_seat (AF_rmB + 432) j W3 regs3 mem3 md3 ly3 k3 z1 z2 seen5 items D1 kids HP3st) as (HR3 & HS3).
  set (E3 := rm_Es regs3 (rm_xsN z2 seen5 5 kids (Z.of_nat (length items)))) in HR3, HS3.
  assert (ER3 : forall n' (r : bv 5), (n' < 32)%nat -> Z.of_nat n' = bv_unsigned r -> ew E3 n' = getr regs3 r)
    by (intros n' r Hn' Hr; exact (rm_Es_reg regs3 _ n' r Hn' Hr)).
  pose proof HP3st as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H3_2 & H3_3 & H3_4 & H3_8 & H3_9 & H3_18 & H3_19 & H3_20 & H3_21
    & H3_22 & H3_23 & H3_24 & H3_25 & H3_27).
  assert (U3_2 : bv_unsigned (ew E3 2) = spZ regs - 128)
    by (rewrite (ER3 2%nat 2%bv), H3_2 by (lia || reflexivity); apply unsigned_lit_small; lia).
  assert (U3_9 : bv_unsigned (ew E3 9) = z1)
    by (rewrite (ER3 9%nat 9%bv), H3_9 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; lia).
  assert (E3_47 : ew E3 47 = Z_to_bv 64 SHADOW_OFF)
    by exact (rm_Es_x regs3 (rm_xsN z2 seen5 5 kids (Z.of_nat (length items))) 2 ltac:(cbn; lia) ltac:(lia)).
  assert (E3_49 : ew E3 49 = Z_to_bv 64 kids)
    by exact (rm_Es_x regs3 (rm_xsN z2 seen5 5 kids (Z.of_nat (length items))) 4 ltac:(cbn; lia) ltac:(lia)).
  assert (UB3_47 : bv_unsigned (ew E3 47) = SHADOW_OFF) by (rewrite E3_47; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U3_49 : bv_unsigned (ew E3 49) = kids) by (rewrite E3_49; apply unsigned_lit_small; exact (proj1 Hk)).
  assert (U3_24 : bv_unsigned (ew E3 24) = 56 * Z.of_nat j)
    by (rewrite (ER3 24%nat 24%bv), H3_24 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; lia).
  assert (U3_26 : bv_unsigned (ew E3 26) = 56 * Z.of_nat j)
    by (rewrite (ER3 26%nat 26%bv), G3_26 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; lia).
  assert (HEIp3 : img_env VAL A_LIM E3) by (subst E3; unfold rm_Es; apply Eimg_env).
  assert (SHOK3 : sh_ok SEGS (SOff 47 0) [] E3 (mrestrict (w_H W3) mem3)) by constructor.
  assert (Hsp3 : spZ regs3 = spZ regs - 128) by (unfold spZ at 1; rewrite H3_2; apply unsigned_lit_small; lia).
  pose proof (rm_sub_rslot_now z1 _ D1 _ _ _ _ _ regs3 0 Hs1 (proj1 HI6) Hsp3 ltac:(lia)) as (_ & _ & _ & _ & HRA3 & _).
  pose proof HI6 as ((HJ6 & Eab6) & HLd6 & HPM6 & _).
  change (Z_to_bv 64 (BASE + 4152)) with (Z_to_bv 64 (BASE + (AF_rmB + 432))).
  (* ---- slot 108: beqz a0 ---- *)
  psrr_branch_tok RUN BR HS3 SHOK3 RM_Bspan.
  + (* a0 = 0: to the back edge *)
    paj_run_to_tok_x_inv RUNTO HS3 HJ6 SHOK3 HPM6 RM_Bspan (AF_rmB + 488); [rm_awr U3_2|].
    clear HG.
    rm_reinv HI6 HS3 HJ6 HPM6 HFr U3_2 HI7. clear HF HFr.
    pose proof (rm_regs_carry E3 _ rm_srP regs3 _ _ _
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 27%bv]
      512 HR3 HS3 ltac:(split; [intros n' Hn'; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity])
      ltac:(vm_compute; reflexivity)) as KC7.
    assert (E3_45 : ew E3 45 = Z_to_bv 64 z2)
      by exact (rm_Es_x regs3 (rm_xsN z2 seen5 5 kids (Z.of_nat (length items))) 0 ltac:(cbn; lia) ltac:(lia)).
    rm_frame_rg HS3 RG7.
    lazymatch type of RG7 with region_ok _ ?E7 _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
      pose proof (rm_slot_of_region E7 _ _ 8 (SOff 45 0) RG7 ltac:(rewrite ?ew_ewset_other by lia; exact U3_2)
        ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hz27;
      lazymatch cs with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
        pose proof (rm_slot_of_region E7 _ _ 16 e16 RG7 ltac:(rewrite ?ew_ewset_other by lia; exact U3_2)
          ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hseen7;
        set (seen7 := bv_unsigned (sv_denot E7 e16)) in Hseen7 end end.
    clear RG7.
    rewrite rm_sv0, ?ew_ewset_other, E3_45, unsigned_lit_small in Hz27 by lia.
    lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into ms7 end.
    pmkst HS3.
    eapply (rm_par_back n IH j W3 (ms_regs ms7) (ms_mem ms7) _ _ _ z1 z2 seen7 items D1 kids Hlen ltac:(lia)).
    split; [exact HI7|]. split; [exact Hseen7|]. split; [apply bv_unsigned_in_range|].
    split; [exact Hz27|]. split; [exact Hz2s|]. split; [exact Rz2|]. split; [exact Hs1|]. split; [exact Hk|]. split; [lia|].
    split; [rewrite (KC7 2%bv) by (cbn; tauto); exact H3_2|].
    split; [rewrite (KC7 3%bv) by (cbn; tauto); exact H3_3|].
    split; [rewrite (KC7 4%bv) by (cbn; tauto); exact H3_4|].
    split; [rewrite (KC7 8%bv) by (cbn; tauto); exact H3_8|].
    split; [rewrite (KC7 9%bv) by (cbn; tauto); exact H3_9|].
    split; [rewrite (KC7 18%bv) by (cbn; tauto); exact H3_18|].
    split; [rewrite (KC7 19%bv) by (cbn; tauto); exact H3_19|].
    split; [rewrite (KC7 20%bv) by (cbn; tauto); exact H3_20|].
    split; [rewrite (KC7 21%bv) by (cbn; tauto); exact H3_21|].
    split; [rewrite (KC7 22%bv) by (cbn; tauto); exact H3_22|].
    split; [rewrite (KC7 23%bv) by (cbn; tauto); exact H3_23|].
    split; [rewrite (KC7 24%bv) by (cbn; tauto); exact H3_24|].
    split; [rewrite (KC7 25%bv) by (cbn; tauto); exact H3_25|].
    rewrite (KC7 27%bv) by (cbn; tauto); exact H3_27.
  + (* a0 <> 0: the shadow of the kids word, the kids word, the traps on kids + 56 j *)
    paj_run_tok_x_inv RUN HS3 HJ6 SHOK3 HPM6 RM_Bspan.
    all: try (rm_awr U3_2).
    all: try (lazymatch goal with |- range_addressable _ _ _ _ =>
      cbn [ms_mem mkst]; rewrite !U_SOff, ?ew_ewset_other by lia; rewrite UB3_47, U3_9, !Z.add_0_r; unfold zcanon, M64;
      rewrite !Z.mod_small by (unfold SHADOW_OFF; lia);
      lazymatch goal with |- range_addressable (rd_of ?sg (mrestrict ?H ?m)) _ _ _ =>
        change (rd_of sg (mrestrict H m)) with (aview sg H m) end;
      eapply range_addressable_sub; [exact HRA3 | lia | lia] end).
    clear HG.
    rm_reinv HI6 HS3 HJ6 HPM6 HFr U3_2 HI7. clear HF HFr.
    rename Hc into Ha0.
    (* slot 113: bltu (56 j + kids) kids, the pointer-overflow trap: refuted *)
    psrr_branch_tok RUN BR HS3 SHOK3 RM_Bspan.
    { exfalso. rewrite branch_ltu_U in Hc.
      repeat first [rewrite U_SAlu in Hc | rewrite U_SMd in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
      cbn [zalu_raw zmd_raw] in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite ?U3_26, ?U3_49, ?Z.add_0_r in Hc.
      rm_zc Hc. rm_ltb Hc; cbn in Hc; try discriminate Hc; lia. }
    clear Hc. paj_run_tok_x_inv RUN HS3 HJ6 SHOK3 HPM6 RM_Bspan; [rm_awr U3_2|].
    clear HG.
    rm_reinv HI7 HS3 HJ6 HPM6 HFr U3_2 HI8. clear HF HFr.
    (* slot 117: beqz ((kids <> 0) xor (56 j + kids = 0)), the null-pointer trap: refuted *)
    psrr_branch_tok RUN BR HS3 SHOK3 RM_Bspan.
    { exfalso. rewrite branch_eq_U in Hc.
      repeat first [rewrite U_SAlu in Hc | rewrite U_SMd in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
      cbn [zalu_raw zmd_raw] in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite ?U3_26, ?U3_49, ?Z.add_0_r in Hc.
      rm_zc Hc. rm_ltb Hc; cbn in Hc; try discriminate Hc; lia. }
    (* slots 118 .. 120: a0 = kids + 56 j, a1 = "value", the call pj_get (item j, "value") *)
    clear Hc. paj_run_tok_x_inv RUN HS3 HJ6 SHOK3 HPM6 RM_Bspan; [rm_awr U3_2|].
    clear HG.
    rm_reinv HI8 HS3 HJ6 HPM6 HFr U3_2 HI9. clear HF HFr.
    pose proof (rm_regs_carry_ok E3 _ rm_srP regs3 _ _ _
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 27%bv]
      512 HR3 HS3 ltac:(split; [intros n' Hn'; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity])
      ltac:(vm_compute; reflexivity)) as KC9.
    prreg HS3 (1%bv : bv 5) R1'. rm_rawreg HS3 (10%bv : bv 5) N10'. rm_rawreg HS3 (11%bv : bv 5) N11'.
    assert (E3_45 : ew E3 45 = Z_to_bv 64 z2)
      by exact (rm_Es_x regs3 (rm_xsN z2 seen5 5 kids (Z.of_nat (length items))) 0 ltac:(cbn; lia) ltac:(lia)).
    rm_frame_rg HS3 RG9.
    lazymatch type of RG9 with region_ok _ ?E9 _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
      pose proof (rm_slot_of_region E9 _ _ 8 (SOff 45 0) RG9 ltac:(rewrite ?ew_ewset_other by lia; exact U3_2)
        ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hz29;
      lazymatch cs with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
        pose proof (rm_slot_of_region E9 _ _ 16 e16 RG9 ltac:(rewrite ?ew_ewset_other by lia; exact U3_2)
          ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hseen9;
        set (seen9 := bv_unsigned (sv_denot E9 e16)) in Hseen9 end end.
    clear RG9.
    rewrite rm_sv0, ?ew_ewset_other, E3_45, unsigned_lit_small in Hz29 by lia.
    lazymatch type of HS3 with st_ok _ _ _ (restrict _ ?msq) => rename msq into ms9 end.
    assert (Hsp9 : spZ (ms_regs ms9) = spZ regs - 128)
      by (unfold spZ at 1; rewrite (KC9 2%bv) by (cbn; tauto); rewrite H3_2; apply unsigned_lit_small; lia).
    eapply SRr_bind.
    { eapply (rm_call_inv false W3 _ _ ms9 ly3 _ _ (kids + 56 * Z.of_nat j) 0x11160 [118; 97; 108; 117; 101] u Du
        (AF_rmB + 484) HS3 eq_refl eq_refl HI9 Hsp9).
      - rewrite (KC9 3%bv) by (cbn; tauto). exact H3_3.
      - rewrite (KC9 4%bv) by (cbn; tauto). exact H3_4.
      - exact R1'.
      - unfold AF_rmB, RMB_SLOT. lia.
      - unfold AF_rmB, RMB_SLOT. reflexivity.
      - vm_compute. reflexivity.
      - left. unfold s0Z. rewrite (KC9 8%bv) by (cbn; tauto). rewrite H3_8. unfold w64. rewrite unsigned_lit_small by lia. lia.
      - apply (rm_U_reg _ _ _ _ N10'); [|lia].
        rewrite U_SAlu, !U_SOff, ?ew_ewset_other by lia. rewrite U3_24, U3_49, !Z.add_0_r. cbn [zalu_raw]. unfold zcanon, M64.
        rewrite !Z.mod_small by lia. lia.
      - rewrite N11', rm_sv0, ?ew_ewset_other by lia. rewrite (ER3 21%nat 21%bv), H3_21 by (lia || reflexivity). try (f_equal; lia).
      - cbn [rm_keytab In]. repeat first [left; reflexivity | right].
      - right; right. exact Hsu. }
    cbv beta. intros W4 c4 _ (ly4 & regs4 & mem4 & md4 & k4 & -> & HI10 & HP10 & HKF10 & _).
    rewrite R1'.
    rm_pres HP10 2 (2%bv : bv 5) T2. rm_pres HP10 3 (3%bv : bv 5) T3. rm_pres HP10 4 (4%bv : bv 5) T4.
    rm_pres HP10 8 (8%bv : bv 5) T8. rm_pres HP10 9 (9%bv : bv 5) T9. rm_pres HP10 18 (18%bv : bv 5) T18.
    rm_pres HP10 19 (19%bv : bv 5) T19. rm_pres HP10 20 (20%bv : bv 5) T20. rm_pres HP10 21 (21%bv : bv 5) T21.
    rm_pres HP10 22 (22%bv : bv 5) T22. rm_pres HP10 23 (23%bv : bv 5) T23. rm_pres HP10 24 (24%bv : bv 5) T24.
    rm_pres HP10 25 (25%bv : bv 5) T25. rm_pres HP10 27 (27%bv : bv 5) T27.
    assert (HP4st : rm_parst j W4 regs4 mem4 md4 ly4 k4 z1 z2 seen9 items D1 kids).
    { split; [exact HI10|]. split; [apply HKF10; [lia | cbn; lia | exact Hseen9]|]. split; [apply bv_unsigned_in_range|].
      split; [apply HKF10; [lia | cbn; lia | exact Hz29]|]. split; [exact Hz2s|]. split; [exact Rz2|]. split; [exact Hs1|].
      split; [exact Hk|]. split; [lia|].
      split; [rewrite T2, (KC9 2%bv) by (cbn; tauto); exact H3_2|].
      split; [rewrite T3, (KC9 3%bv) by (cbn; tauto); exact H3_3|].
      split; [rewrite T4, (KC9 4%bv) by (cbn; tauto); exact H3_4|].
      split; [rewrite T8, (KC9 8%bv) by (cbn; tauto); exact H3_8|].
      split; [rewrite T9, (KC9 9%bv) by (cbn; tauto); exact H3_9|].
      split; [rewrite T18, (KC9 18%bv) by (cbn; tauto); exact H3_18|].
      split; [rewrite T19, (KC9 19%bv) by (cbn; tauto); exact H3_19|].
      split; [rewrite T20, (KC9 20%bv) by (cbn; tauto); exact H3_20|].
      split; [rewrite T21, (KC9 21%bv) by (cbn; tauto); exact H3_21|].
      split; [rewrite T22, (KC9 22%bv) by (cbn; tauto); exact H3_22|].
      split; [rewrite T23, (KC9 23%bv) by (cbn; tauto); exact H3_23|].
      split; [rewrite T24, (KC9 24%bv) by (cbn; tauto); exact H3_24|].
      split; [rewrite T25, (KC9 25%bv) by (cbn; tauto); exact H3_25|].
      rewrite T27, (KC9 27%bv) by (cbn; tauto); exact H3_27. }
    destruct (rm_par_seat (AF_rmB + 484) j W4 regs4 mem4 md4 ly4 k4 z1 z2 seen9 items D1 kids HP4st) as (HR4 & HS4).
    set (E4 := rm_Es regs4 (rm_xsN z2 seen9 5 kids (Z.of_nat (length items)))) in HR4, HS4.
    pose proof HP4st as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H4_2 & H4_3 & H4_4 & H4_8 & H4_9 & H4_18 & H4_19 & H4_20
      & H4_21 & H4_22 & H4_23 & H4_24 & H4_25 & H4_27).
    assert (EW4_2 : ew E4 2 = getr regs4 2%bv)
      by exact (rm_Es_reg regs4 (rm_xsN z2 seen9 5 kids (Z.of_nat (length items))) 2 2%bv ltac:(lia) eq_refl).
    assert (U4_2 : bv_unsigned (ew E4 2) = spZ regs - 128)
      by (rewrite EW4_2, H4_2; apply unsigned_lit_small; lia).
    assert (E4_45 : ew E4 45 = Z_to_bv 64 z2)
      by exact (rm_Es_x regs4 (rm_xsN z2 seen9 5 kids (Z.of_nat (length items))) 0 ltac:(cbn; lia) ltac:(lia)).
    assert (HEIp4 : img_env VAL A_LIM E4) by (subst E4; unfold rm_Es; apply Eimg_env).
    assert (SHOK4 : sh_ok SEGS (SOff 47 0) [] E4 (mrestrict (w_H W4) mem4)) by constructor.
    pose proof HI10 as ((HJ10 & Eab10) & HLd10 & HPM10 & _).
    change (Z_to_bv 64 (BASE + 4204)) with (Z_to_bv 64 (BASE + (AF_rmB + 484))).
    (* ---- slot 121: the result's flag, to the back edge ---- *)
    paj_run_to_tok_x_inv RUNTO HS4 HJ10 SHOK4 HPM10 RM_Bspan (AF_rmB + 488); [rm_awr U4_2|].
    clear HG.
    rm_reinv HI10 HS4 HJ10 HPM10 HFr U4_2 HI11. clear HF HFr.
    pose proof (rm_regs_carry E4 _ rm_srP regs4 _ _ _
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 27%bv]
      512 HR4 HS4 ltac:(split; [intros n' Hn'; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity])
      ltac:(vm_compute; reflexivity)) as KC11.
    rm_frame_rg HS4 RG11.
    lazymatch type of RG11 with region_ok _ ?E11 _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
      pose proof (rm_slot_of_region E11 _ _ 8 (SOff 45 0) RG11 ltac:(rewrite ?ew_ewset_other by lia; exact U4_2)
        ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hz211;
      lazymatch cs with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
        pose proof (rm_slot_of_region E11 _ _ 16 e16 RG11 ltac:(rewrite ?ew_ewset_other by lia; exact U4_2)
          ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hseen11;
        set (seen11 := bv_unsigned (sv_denot E11 e16)) in Hseen11 end end.
    clear RG11.
    rewrite rm_sv0, ?ew_ewset_other, E4_45, unsigned_lit_small in Hz211 by lia.
    lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into ms11 end.
    pmkst HS4.
    eapply (rm_par_back n IH j W4 (ms_regs ms11) (ms_mem ms11) _ _ _ z1 z2 seen11 items D1 kids Hlen ltac:(lia)).
    split; [exact HI11|]. split; [exact Hseen11|]. split; [apply bv_unsigned_in_range|].
    split; [exact Hz211|]. split; [exact Hz2s|]. split; [exact Rz2|]. split; [exact Hs1|]. split; [exact Hk|]. split; [lia|].
    split; [rewrite (KC11 2%bv) by (cbn; tauto); exact H4_2|].
    split; [rewrite (KC11 3%bv) by (cbn; tauto); exact H4_3|].
    split; [rewrite (KC11 4%bv) by (cbn; tauto); exact H4_4|].
    split; [rewrite (KC11 8%bv) by (cbn; tauto); exact H4_8|].
    split; [rewrite (KC11 9%bv) by (cbn; tauto); exact H4_9|].
    split; [rewrite (KC11 18%bv) by (cbn; tauto); exact H4_18|].
    split; [rewrite (KC11 19%bv) by (cbn; tauto); exact H4_19|].
    split; [rewrite (KC11 20%bv) by (cbn; tauto); exact H4_20|].
    split; [rewrite (KC11 21%bv) by (cbn; tauto); exact H4_21|].
    split; [rewrite (KC11 22%bv) by (cbn; tauto); exact H4_22|].
    split; [rewrite (KC11 23%bv) by (cbn; tauto); exact H4_23|].
    split; [rewrite (KC11 24%bv) by (cbn; tauto); exact H4_24|].
    split; [rewrite (KC11 25%bv) by (cbn; tauto); exact H4_25|].
    rewrite (KC11 27%bv) by (cbn; tauto); exact H4_27.
Qed.
Lemma rm_par_loop : forall n, rm_parP n.
Proof.
induction n as [|n IHn]; apply rm_par_iter; [lia | intros Hn; replace (Datatypes.S n - 1)%nat with n by lia; exact IHn].
Qed.

Lemma rm_after_c4 : forall W2 regsL mem2 md2 ly2 k z1 z2 z4 seen,
  rm_c4st W2 regsL mem2 md2 ly2 k z1 z2 z4 seen ->
  SRr SEGS W2 (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_rmB + 212))) mem2 (seg_rom SEGS)) md2) rm_goal.
Proof.
intros W2 regsL mem2 md2 ly2 k z1 z2 z4 seen
  (HI & Hseen & Hseen0 & Hz2v & G2 & G3 & G4 & G8 & G9 & G18 & G20 & G10 & Hz1s & Hz2s & Hz4s & Rz1 & Rz2 & Rz4).
pose proof rm_stks as (FS & FS1 & FS2). pose proof rm_sp_bounds as (SB1 & SB2 & SB3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
pose proof HI as ((HJ & Eab) & HLd & HPM & HFR).
pose proof (rm_seatT regsL W2 mem2 ly2 md2 k (AF_rmB + 212) z2 seen HI Hseen Hseen0 Hz2v Rz2 G2) as HS.
set (EC := rm_Es regsL [z2; seen]) in HS.
assert (ERC : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EC n = getr regsL r)
  by (intros n r Hn Hr; exact (rm_Es_reg regsL [z2; seen] n r Hn Hr)).
assert (UC : bv_unsigned (ew EC 2) = spZ regs - 128)
  by (rewrite (ERC 2%nat 2%bv), G2 by (lia || reflexivity); apply unsigned_lit_small; lia).
assert (EC243 : ew EC 243 = Z_to_bv 64 (VAL (A_OBJ 2))) by (subst EC; unfold rm_Es; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EC45 : ew EC 45 = Z_to_bv 64 z2) by exact (rm_Es_x regsL [z2; seen] 0 ltac:(cbn; lia) ltac:(lia)).
assert (EC46 : ew EC 46 = Z_to_bv 64 seen) by exact (rm_Es_x regsL [z2; seen] 1 ltac:(cbn; lia) ltac:(lia)).
assert (HEIC : img_env VAL A_LIM EC) by (subst EC; unfold rm_Es; apply Eimg_env).
assert (SHOKC : sh_ok SEGS (SOff 20 0) [] EC (mrestrict (w_H W2) mem2)) by constructor.
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_rm_B PA B PST ARx _ LAWS _ RLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_rm_B PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
pose proof (pa_val_range (A_OBJ 2)) as RV2.
(* ---- slots 53 .. 55: a1 = "id", the call pj_get_str (plugin, "id") ---- *)
paj_run_tok_x_inv RUN HS HJ SHOKC HPM RM_Bspan; [rm_awr UC|].
clear HG.
rm_reinv HI HS HJ HPM HFr UC HI1. clear HF HFr.
assert (HAEC : env_agree 32 (Ereg regsL (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [z2; seen])) EC)
  by (split; [intros n Hn; subst EC; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS EC _ _ regsL _ [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 20%bv] HS HAEC
  ltac:(vm_compute; reflexivity)) as KC.
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msq) => rename msq into ms1 end.
rm_frame_rg HS RG1.
pose proof (rm_slot_of_region EC _ _ 8 (SOff 45 0) RG1 UC ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hz21.
pose proof (rm_slot_of_region EC _ _ 16 (SOff 46 0) RG1 UC ltac:(cbn [In]; repeat first [left; reflexivity | right]))
  as Hseen1.
clear RG1.
rewrite rm_sv0, EC45, unsigned_lit_small in Hz21 by lia.
rewrite rm_sv0, EC46, unsigned_lit_small in Hseen1 by lia.
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs - 128)
  by (unfold spZ at 1; rewrite (KC 2%bv) by (cbn; tauto); rewrite G2; apply unsigned_lit_small; lia).
assert (HO4 : exists tt Dt, z4 = 0 \/ (z4 = doc /\ tt = t /\ Dt = D) \/ rm_sub z4 tt Dt)
  by (destruct Hz4s as [-> | (v4 & D4 & Hs4)]; [exists t, D; left; reflexivity | exists v4, D4; right; right; exact Hs4]).
destruct HO4 as (tt4 & Dt4 & HO4).
(* ---- the call pj_get_str (plugin, "id") (slot 55) ---- *)
eapply SRr_bind.
{ eapply (rm_call_inv true W2 EC _ ms1 ly2 _ _ z4 0x11040 [105; 100] tt4 Dt4 (AF_rmB + 224) HS eq_refl eq_refl HI1 Hsp1).
  - rewrite (KC 3%bv) by (cbn; tauto). exact G3.
  - rewrite (KC 4%bv) by (cbn; tauto). exact G4.
  - exact R1.
  - unfold AF_rmB, RMB_SLOT. lia.
  - unfold AF_rmB, RMB_SLOT. reflexivity.
  - vm_compute. reflexivity.
  - right; left. unfold s0Z. rewrite (KC 8%bv), G8 by (cbn; tauto). unfold w64. rewrite Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    pose proof rm_entry_stk as (_ & _ & _ & _ & _ & H47' & _ & Htop1 & Htop2). cbn. lia.
  - rewrite R10, (ERC 10%nat 10%bv), G10 by (lia || reflexivity). reflexivity.
  - rewrite R11, EC243, unsigned_lit_small by lia. reflexivity.
  - cbn [rm_keytab In]. repeat first [left; reflexivity | right].
  - exact HO4. }
cbv beta. intros W3 c3 _ (ly3 & regs3 & mem3 & md3 & k3 & -> & HI3 & HP3 & HKF3 & _).
rewrite R1.
rm_pres HP3 2 (2%bv : bv 5) P2. rm_pres HP3 3 (3%bv : bv 5) P3. rm_pres HP3 4 (4%bv : bv 5) P4.
rm_pres HP3 8 (8%bv : bv 5) P8. rm_pres HP3 9 (9%bv : bv 5) P9. rm_pres HP3 20 (20%bv : bv 5) P20.
assert (G3_2 : getr regs3 2 = Z_to_bv 64 (spZ regs - 128)) by (rewrite P2, (KC 2%bv) by (cbn; tauto); exact G2).
assert (G3_3 : getr regs3 3 = getr regs 3) by (rewrite P3, (KC 3%bv) by (cbn; tauto); exact G3).
assert (G3_4 : getr regs3 4 = getr regs 4) by (rewrite P4, (KC 4%bv) by (cbn; tauto); exact G4).
assert (G3_9 : getr regs3 9 = w64 z1) by (rewrite P9, (KC 9%bv) by (cbn; tauto); exact G9).
assert (G3_20 : getr regs3 20 = w64 SHADOW_OFF) by (rewrite P20, (KC 20%bv) by (cbn; tauto); exact G20).
assert (Hseen3 : val_mem SEGS (rdW W3 mem3) (spZ regs - 128 + 16) 8 seen) by (apply HKF3; [lia | cbn; lia | exact Hseen1]).
assert (Hz23 : val_mem SEGS (rdW W3 mem3) (spZ regs - 128 + 8) 8 z2) by (apply HKF3; [lia | cbn; lia | exact Hz21]).
change (Z_to_bv 64 (BASE + 3944)) with (Z_to_bv 64 (BASE + (AF_rmB + 224))).
pose proof HI3 as ((HJ3 & Eab3) & HLd3 & HPM3 & HFR3).
destruct Hz1s as [Hz10 | (v1 & D1 & Hs1)].
- (* z1 = 0: no params *)
  subst z1.
  pose proof (rm_seatT regs3 W3 mem3 ly3 md3 k3 (AF_rmB + 224) z2 seen HI3 Hseen3 Hseen0 Hz23 Rz2 G3_2) as HS3.
  set (E3 := rm_Es regs3 [z2; seen]) in HS3.
  assert (ER3 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs3 r)
    by (intros n r Hn Hr; exact (rm_Es_reg regs3 [z2; seen] n r Hn Hr)).
  assert (U3 : bv_unsigned (ew E3 2) = spZ regs - 128)
    by (rewrite (ER3 2%nat 2%bv), G3_2 by (lia || reflexivity); apply unsigned_lit_small; lia).
  assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; unfold rm_Es; apply Eimg_env).
  assert (SHOK3 : sh_ok SEGS (SOff 20 0) [] E3 (mrestrict (w_H W3) mem3)) by constructor.
  (* ---- slots 56 .. 60: the counter, beqz s1 ---- *)
  paj_run_tok_x_inv RUN HS3 HJ3 SHOK3 HPM3 RM_Bspan; [rm_awr U3|].
  clear HG.
  rm_reinv HI3 HS3 HJ3 HPM3 HFr U3 HI4. clear HF HFr.
  psrr_branch_tok RUN BR HS3 SHOK3 RM_Bspan.
  + (* taken: to the tail *)
    paj_run_to_tok_x_inv RUNTO HS3 HJ3 SHOK3 HPM3 RM_Bspan (AF_rmB + 544); [rm_awr U3|].
    clear HG.
    rm_reinv HI4 HS3 HJ3 HPM3 HFr U3 HI5. clear HF HFr.
    assert (HAE3 : env_agree 32 (Ereg regs3 (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [z2; seen])) E3)
      by (split; [intros n Hn; subst E3; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    pose proof (regs_kept_of_st_ok_pi (PI := PA) E3 _ _ regs3 _ [2%bv; 3%bv; 4%bv] HS3 HAE3
      ltac:(vm_compute; reflexivity)) as K5.
    assert (E3_45 : ew E3 45 = Z_to_bv 64 z2) by exact (rm_Es_x regs3 [z2; seen] 0 ltac:(cbn; lia) ltac:(lia)).
    rm_frame_rg HS3 RG5.
    pose proof (rm_slot_of_region E3 _ _ 8 (SOff 45 0) RG5 U3 ltac:(cbn [In]; repeat first [left; reflexivity | right]))
      as Hz25.
    rewrite rm_sv0, E3_45, unsigned_lit_small in Hz25 by lia.
    lazymatch type of RG5 with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
      pose proof (rm_slot_of_region E3 _ _ 16 e16 RG5 U3 ltac:(cbn [In]; repeat first [left; reflexivity | right]))
        as Hseen5; set (seen5 := bv_unsigned (sv_denot E3 e16)) in Hseen5 end.
    clear RG5.
    lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into ms5 end.
    pmkst HS3.
    eapply (rm_tail W3 (ms_regs ms5) (ms_mem ms5) _ _ _ z2 seen5).
    split; [exact HI5|]. split; [exact Hseen5|]. split; [apply bv_unsigned_in_range|]. split; [exact Hz25|].
    split; [rewrite (K5 2%bv) by (cbn; tauto); exact G3_2|].
    split; [rewrite (K5 3%bv) by (cbn; tauto); exact G3_3|].
    split; [rewrite (K5 4%bv) by (cbn; tauto); exact G3_4|].
    split; [exact Hz2s | exact Rz2].
  + (* not taken: z1 <> 0, impossible *)
    exfalso. rewrite branch_eq_U, U_SLit in Hc. unfold U in Hc.
    rewrite (rm_w64_off E3 9 0 0) in Hc by (rewrite (ER3 9%nat 9%bv) by (lia || reflexivity); exact G3_9).
    unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia. vm_compute in Hc. discriminate Hc.
- (* z1 <> 0: the params node below the root *)
  pose proof (rm_sub_range z1 v1 D1 Hs1) as (Z1lo & Z1hi).
  pose proof (rm_sub_now z1 v1 D1 ly3 W3 mem3 md3 k3 Hs1 (proj1 HI3)) as Hn3.
  destruct (rm_node_hdr _ _ _ _ _ Hn3) as (num & str & kids & keys & n & cap & Hh3).
  pose proof Hh3 as ((Hal8 & _) & Hty & _ & _ & Hk & _ & Hnn & _).
  pose proof Hty as (Hty0 & _). pose proof Hk as (Hk0 & _). pose proof Hnn as (Hn0 & _).
  set (EN := rm_Es regs3 (rm_xsN z2 seen (tag v1) kids n)).
  assert (ERN : forall n' (r : bv 5), (n' < 32)%nat -> Z.of_nat n' = bv_unsigned r -> ew EN n' = getr regs3 r)
    by (intros n' r Hn' Hr; exact (rm_Es_reg regs3 (rm_xsN z2 seen (tag v1) kids n) n' r Hn' Hr)).
  assert (HtvN : sv_denot EN (SOff 48 0) = Z_to_bv 64 (tag v1))
    by (rewrite rm_sv0; exact (rm_Es_x regs3 (rm_xsN z2 seen (tag v1) kids n) 3 ltac:(cbn; lia) ltac:(lia))).
  assert (HsrN : regs_ok EN sr_atoms regs3) by (subst EN; unfold rm_Es; apply regs_ok_Eimg_Ereg).
  assert (HBN : bv_unsigned (ew EN 20) = SHADOW_OFF)
    by (rewrite (ERN 20%nat 20%bv), G3_20 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  pose proof (rm_seatN regs3 W3 mem3 ly3 md3 k3 (AF_rmB + 224) z2 seen z1 (tag v1) kids n (SOff 48 0) sr_atoms 20
    HI3 Hseen3 Hseen0 Hz23 Rz2 G3_2 G3_9 ltac:(lia) ltac:(lia) Hal8 Hty Hk Hnn HtvN HsrN HBN) as HS3.
  change (rm_Es regs3 (rm_xsN z2 seen (tag v1) kids n)) with EN in HS3.
  assert (UN : bv_unsigned (ew EN 2) = spZ regs - 128)
    by (rewrite (ERN 2%nat 2%bv), G3_2 by (lia || reflexivity); apply unsigned_lit_small; lia).
  assert (UN9 : bv_unsigned (ew EN 9) = z1)
    by (rewrite (ERN 9%nat 9%bv), G3_9 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; lia).
  assert (HEIN : img_env VAL A_LIM EN) by (subst EN; unfold rm_Es; apply Eimg_env).
  assert (SHOKN : sh_ok SEGS (SOff 20 0) [] EN (mrestrict (w_H W3) mem3)) by constructor.
  assert (Hsp3 : spZ regs3 = spZ regs - 128) by (unfold spZ at 1; rewrite G3_2; apply unsigned_lit_small; lia).
  pose proof (rm_sub_rslot_now z1 v1 D1 ly3 W3 mem3 md3 k3 regs3 0 Hs1 (proj1 HI3) Hsp3 ltac:(lia))
    as (_ & _ & _ & _ & HRA1 & _).
  (* ---- slots 56 .. 69: the counter, beqz s1 and the alignment trap decided by the facts, the shadow of the node's
     type word (an obligation), the type word, bne type 5 ---- *)
  paj_run_tok_x_inv RUN HS3 HJ3 SHOKN HPM3 RM_Bspan.
  all: try (rm_awr UN).
  all: try (lazymatch goal with |- range_addressable _ _ _ _ =>
    cbn [ms_mem mkst]; rewrite !U_SOff, HBN, UN9, !Z.add_0_r; unfold zcanon, M64;
    rewrite !Z.mod_small by (unfold SHADOW_OFF; lia);
    change (rd_of SEGS (rdW W3 mem3)) with (aview SEGS (w_H W3) mem3);
    eapply range_addressable_sub; [exact HRA1 | lia | lia] end).
  clear HG.
  rm_reinv HI3 HS3 HJ3 HPM3 HFr UN HI4. clear HF HFr.
  assert (EN48 : ew EN 48 = Z_to_bv 64 (tag v1)) by exact (rm_Es_x regs3 (rm_xsN z2 seen (tag v1) kids n) 3 ltac:(cbn; lia) ltac:(lia)).
  assert (EN45 : ew EN 45 = Z_to_bv 64 z2) by exact (rm_Es_x regs3 (rm_xsN z2 seen (tag v1) kids n) 0 ltac:(cbn; lia) ltac:(lia)).
  assert (HAEN : env_agree 32 (Ereg regs3 (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64)
      (rm_xsN z2 seen (tag v1) kids n))) EN)
    by (split; [intros n' Hn'; subst EN; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  psrr_branch_tok RUN BR HS3 SHOKN RM_Bspan.
  all: rewrite branch_ne_U, U_SLit in Hc;
    rewrite (rm_tagU _ 48 v1) in Hc by (rewrite ?ew_ewset_other by lia; exact EN48);
    change (zcanon 5) with 5 in Hc.
  + (* taken: not an array; to the tail *)
    paj_run_to_tok_x_inv RUNTO HS3 HJ3 SHOKN HPM3 RM_Bspan (AF_rmB + 544); [rm_awr UN|].
    clear HG.
    rm_reinv HI4 HS3 HJ3 HPM3 HFr UN HI5. clear HF HFr.
    pose proof (regs_kept_of_st_ok_pi (PI := PA) _ _ _ regs3 _ [2%bv; 3%bv; 4%bv] HS3
      ltac:(eapply env_agree_trans; [exact HAEN | split; [intros n' Hn'; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]])
      ltac:(vm_compute; reflexivity)) as K5.
    rm_frame_rg HS3 RG5.
    pose proof (rm_slot_of_region _ _ _ 8 (SOff 45 0) RG5 ltac:(rewrite ?ew_ewset_other by lia; exact UN)
      ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hz25.
    rewrite rm_sv0, ?ew_ewset_other, EN45, unsigned_lit_small in Hz25 by lia.
    lazymatch type of RG5 with region_ok _ ?E5 _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
      lazymatch cs with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
        pose proof (rm_slot_of_region E5 _ _ 16 e16 RG5 ltac:(rewrite ?ew_ewset_other by lia; exact UN)
          ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hseen5;
        set (seen5 := bv_unsigned (sv_denot E5 e16)) in Hseen5 end end.
    clear RG5.
    lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into ms5 end.
    pmkst HS3.
    eapply (rm_tail W3 (ms_regs ms5) (ms_mem ms5) _ _ _ z2 seen5).
    split; [exact HI5|]. split; [exact Hseen5|]. split; [apply bv_unsigned_in_range|]. split; [exact Hz25|].
    split; [rewrite (K5 2%bv) by (cbn; tauto); exact G3_2|].
    split; [rewrite (K5 3%bv) by (cbn; tauto); exact G3_3|].
    split; [rewrite (K5 4%bv) by (cbn; tauto); exact G3_4|].
    split; [exact Hz2s | exact Rz2].
  + (* not taken: an array; to the params loop head *)
    apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hv1 : exists items, v1 = JArr items)
      by (destruct v1; cbn [tag] in Hc; try discriminate Hc; eexists; reflexivity).
    destruct Hv1 as (items & ->).
    destruct (rm_arr_info z1 items D1 Hs1) as (kids0 & cap0 & Hk0e & Hn0e & Hty0e & Hal0 & Hcn0 & Hcap0).
    (* ---- slots 69 .. 83: s8 = 0, s9 = 0, s3 = node + 40, s2 = node + 24, the shadow cells of the count and kids words,
       s0 = "symbol", s5 = "value" ---- *)
    paj_run_to_tok_x_inv RUNTO HS3 HJ3 SHOKN HPM3 RM_Bspan (AF_rmB + 336); [rm_awr UN|].
    clear HG.
    rm_reinv HI4 HS3 HJ3 HPM3 HFr UN HI5. clear HF HFr.
    pose proof (regs_kept_of_st_ok_pi (PI := PA) _ _ _ regs3 _ [2%bv; 3%bv; 4%bv; 9%bv] HS3
      ltac:(eapply env_agree_trans; [exact HAEN | split; [intros n' Hn'; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]])
      ltac:(vm_compute; reflexivity)) as K6.
    rm_rawreg HS3 (8%bv : bv 5) N8. rm_rawreg HS3 (18%bv : bv 5) N18. rm_rawreg HS3 (19%bv : bv 5) N19.
    rm_rawreg HS3 (20%bv : bv 5) N20. rm_rawreg HS3 (21%bv : bv 5) N21. rm_rawreg HS3 (22%bv : bv 5) N22.
    rm_rawreg HS3 (23%bv : bv 5) N23. rm_rawreg HS3 (24%bv : bv 5) N24. rm_rawreg HS3 (25%bv : bv 5) N25.
    rm_rawreg HS3 (27%bv : bv 5) N27.
    assert (EN243 : ew EN 243 = Z_to_bv 64 (VAL (A_OBJ 2))) by (subst EN; unfold rm_Es; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
    assert (EN9 : ew EN 9 = w64 z1) by (rewrite (ERN 9%nat 9%bv) by (lia || reflexivity); exact G3_9).
    pose proof (@YM05.alloc_ceiling_lt rc) as CLT.
    rm_frame_rg HS3 RG6.
    lazymatch type of RG6 with region_ok _ ?E6 _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
      pose proof (rm_slot_of_region E6 _ _ 8 (SOff 45 0) RG6 ltac:(rewrite ?ew_ewset_other by lia; exact UN)
        ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hz26;
      lazymatch cs with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
        pose proof (rm_slot_of_region E6 _ _ 16 e16 RG6 ltac:(rewrite ?ew_ewset_other by lia; exact UN)
          ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hseen6;
        set (seen6 := bv_unsigned (sv_denot E6 e16)) in Hseen6 end end.
    clear RG6.
    rewrite rm_sv0, ?ew_ewset_other, EN45, unsigned_lit_small in Hz26 by lia.
    lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into ms6 end.
    pmkst HS3.
    eapply (rm_par_loop (length items - 0)%nat 0%nat W3 (ms_regs ms6) (ms_mem ms6) _ _ _ z1 z2 seen6 items D1 kids0 eq_refl).
    split; [exact HI5|]. split; [exact Hseen6|]. split; [apply bv_unsigned_in_range|].
    split; [exact Hz26|]. split; [exact Hz2s|]. split; [exact Rz2|]. split; [exact Hs1|]. split; [exact Hk0e|].
    split; [lia|].
    split; [rewrite (K6 2%bv) by (cbn; tauto); exact G3_2|].
    split; [rewrite (K6 3%bv) by (cbn; tauto); exact G3_3|].
    split; [rewrite (K6 4%bv) by (cbn; tauto); exact G3_4|].
    split; [rewrite N8, (rm_w64_off _ 243 (VAL (A_OBJ 2)) _) by (rewrite ?ew_ewset_other by lia; exact EN243);
      f_equal; lia|].
    split; [rewrite (K6 9%bv) by (cbn; tauto); exact G3_9|].
    split; [rewrite N18, (rm_w64_off _ 9 z1 _) by (rewrite ?ew_ewset_other by lia; exact EN9); reflexivity|].
    split; [rewrite N19, (rm_w64_off _ 9 z1 _) by (rewrite ?ew_ewset_other by lia; exact EN9); reflexivity|].
    split; [apply (rm_U_reg _ _ _ _ N20); [apply rm_shxc_U; [rewrite ?ew_ewset_other by lia; exact HBN
      | rewrite ?ew_ewset_other by lia; rewrite UN9; reflexivity | lia] | unfold SHADOW_OFF;
      pose proof (Z.div_pos (z1 + 24) 8 ltac:(lia) ltac:(lia)); assert ((z1 + 24) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); lia]|].
    split; [rewrite N21, (rm_w64_off _ 243 (VAL (A_OBJ 2)) _) by (rewrite ?ew_ewset_other by lia; exact EN243);
      f_equal; lia|].
    split; [apply (rm_U_reg _ _ _ _ N22); [rewrite (rm_shxc_U _ 20 9 0 z1); [reflexivity | rewrite ?ew_ewset_other by lia; exact HBN
      | rewrite ?ew_ewset_other by lia; rewrite UN9; lia | lia] | unfold SHADOW_OFF;
      pose proof (Z.div_pos z1 8 ltac:(lia) ltac:(lia)); assert (z1 / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); lia]|].
    split; [rewrite N23; reflexivity|].
    split; [rewrite N24; reflexivity|].
    split; [rewrite N25; reflexivity|].
    apply (rm_U_reg _ _ _ _ N27); [apply rm_shxc_U; [rewrite ?ew_ewset_other by lia; exact HBN
      | rewrite ?ew_ewset_other by lia; rewrite UN9; reflexivity | lia] | unfold SHADOW_OFF;
      pose proof (Z.div_pos (z1 + 40) 8 ltac:(lia) ltac:(lia)); assert ((z1 + 40) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); lia].
Qed.

Lemma rm_top_iter : forall i, (i <= 5)%nat -> ((i < 5)%nat -> rm_topP (Datatypes.S i)) -> rm_topP i.
Proof.
intros i Hi5 IH W2 regsL mem2 md2 ly2 k z1 z2 seen
  (HI & Hseen & Hseen0 & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & Hz1 & Hz2 & Rz1 & Rz2).
pose proof rm_stks as (FS & FS1 & FS2). pose proof rm_sp_bounds as (SB1 & SB2 & SB3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_value rc) as [[CL CH] _].
pose proof HI as ((HJ & Eab) & HLd & HPM & HFR).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kpres & _).
assert (Hi6 : (i < 6)%nat) by lia.
destruct (rm_top_at ly2 S Hp W2 mem2 md2 HAR2 (rm_rod_now ly2 W2 mem2 md2 k (conj HJ Eab)) i Hi6) as [Htv Hts].
pose proof RM_IMG as (_ & (Ht1 & Ht2 & Ht3) & _).
pose proof rm_pa_top_al as Hal. pose proof rm_pa_o2 as Ho2. unfold IMG_LO_B in Ho2.
pose proof (pa_val_range (A_OBJ 3)) as RV3.
assert (Htlow : VAL (A_OBJ 3) + 48 <= kLowMemEnd).
{ destruct (Ht3 (VAL (A_OBJ 3) + 47) ltac:(lia)) as (Hro & _).
  pose proof (@pa_segs_low _ _ PA _ (rm_ro_img _ Hro)) as HL'. unfold kLowMemEnd in *. lia. }
unfold kLowMemEnd in Htlow.
set (cell := SHADOW_OFF + (VAL (A_OBJ 3) + 8 * Z.of_nat i) / 8).
assert (Hcell : SHADOW_OFF <= cell < SHADOW_OFF + 2 ^ 28).
{ subst cell. pose proof (Z.div_pos (VAL (A_OBJ 3) + 8 * Z.of_nat i) 8 ltac:(lia) ltac:(lia)).
  assert ((VAL (A_OBJ 3) + 8 * Z.of_nat i) / 8 < 2 ^ 28) by (apply Z.div_lt_upper_bound; lia). lia. }
unfold SHADOW_OFF in Hcell.
set (E5 := rm_Es regsL (rm_xs35 i seen)).
assert (E5_45 : ew E5 45 = Z_to_bv 64 (VAL (A_OBJ 3) + 8 * Z.of_nat i))
  by exact (rm_Es_x regsL (rm_xs35 i seen) 0 ltac:(cbn; lia) ltac:(lia)).
assert (E5_46 : ew E5 46 = Z_to_bv 64 (VAL (A_OBJ 2) + 0x11020 + 32 * Z.of_nat i))
  by exact (rm_Es_x regsL (rm_xs35 i seen) 1 ltac:(cbn; lia) ltac:(lia)).
assert (E5_47 : ew E5 47 = Z_to_bv 64 seen) by exact (rm_Es_x regsL (rm_xs35 i seen) 2 ltac:(cbn; lia) ltac:(lia)).
assert (E5_48 : ew E5 48 = Z_to_bv 64 cell) by exact (rm_Es_x regsL (rm_xs35 i seen) 3 ltac:(cbn; lia) ltac:(lia)).
assert (U5 : bv_unsigned (ew E5 2) = spZ regs - 128)
  by (subst E5; rewrite (rm_Es_reg _ _ 2 2%bv) by (lia || reflexivity); rewrite G2; apply unsigned_lit_small; lia).
assert (U5_20 : bv_unsigned (ew E5 20) = SHADOW_OFF)
  by (subst E5; rewrite (rm_Es_reg _ _ 20 20%bv) by (lia || reflexivity); rewrite G20; unfold w64;
      apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U5_45 : bv_unsigned (ew E5 45) = VAL (A_OBJ 3) + 8 * Z.of_nat i) by (rewrite E5_45; apply unsigned_lit_small; lia).
assert (U5_48 : bv_unsigned (ew E5 48) = cell) by (rewrite E5_48; apply unsigned_lit_small; lia).
assert (HR5 : regs_ok E5 rm_sr35 regsL).
{ unfold rm_sr35. apply rm_regs_ok_set; [apply rm_regs_ok_set; [subst E5; unfold rm_Es; apply regs_ok_Eimg_Ereg|]|].
  - apply (rm_reg_U E5 _ _ (VAL (A_OBJ 3) + 8 * Z.of_nat i) G19); [lia|].
    rewrite U_SOff, U5_45, Z.add_0_r. unfold zcanon, M64. apply Z.mod_small. lia.
  - apply (rm_reg_U E5 _ _ cell G21); [lia|]. rewrite U_SOff, U5_48, Z.add_0_r. unfold zcanon, M64. apply Z.mod_small. lia. }
assert (RT : region_ok SEGS E5 (rdW W2 mem2) rm_topreg).
{ unfold region_ok, rm_topreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  assert (B45 : base_val E5 (Some 45%nat) = VAL (A_OBJ 3) + 8 * Z.of_nat i) by (cbn [base_val]; exact U5_45).
  rewrite B45. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E5 _ (VAL (A_OBJ 3) + 8 * Z.of_nat i) 0 8 (SOff 46 0) (VAL (A_OBJ 2) + 0x11020 + 32 * Z.of_nat i));
  [cbn [sv_denot]; rewrite E5_46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
  rewrite Z.add_0_r. exact Htv. }
assert (CK16 : YP09.chunk_ok SEGS E5 (rdW W2 mem2) (spZ regs - 128) (YP09.mkChunk 16 (CVal 8 (SOff 47 0)))).
{ apply (chunk_ok_val SEGS E5 _ (spZ regs - 128) 16 8 (SOff 47 0) seen);
  [cbn [sv_denot]; rewrite E5_47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hseen]. }
assert (RC : region_ok SEGS E5 (rdW W2 mem2) (rm_cellreg 48)).
{ unfold region_ok, rm_cellreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  assert (B48 : base_val E5 (Some 48%nat) = cell) by (cbn [base_val]; exact U5_48).
  rewrite B48. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E5 _ cell 0 1 (SLit 0) 0); [reflexivity | cbn; lia | lia |].
  rewrite Z.add_0_r. apply rm_val1. exact Hts. }
assert (HS5 : st_ok_pi SEGS VAL E5 (mkSS (AF_rmB + 140) rm_sr35 [rm_frame_region [YP09.mkChunk 16 (CVal 8 (SOff 47 0))];
    rm_topreg; rm_cellreg 48] None rm_facts35)
  (restrict (w_H W2) (mkst regsL (Z_to_bv 64 (BASE + (AF_rmB + 140))) mem2 (seg_rom SEGS)))).
{ apply rm_seat_sr; [exact HR5 | exact G2 | exact HFR | intros a Ha; apply Kpres; rewrite FS; lia | constructor; [exact CK16 | constructor]
  | vm_compute; reflexivity | constructor; [exact RT | constructor; [exact RC | constructor]] | | ].
  - change (rm_Es regsL (rm_xs35 i seen)) with E5.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, rm_frame_region, rm_topreg, rm_cellreg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U5, U5_45, U5_48.
    repeat split; try exact I; lia.
  - change (rm_Es regsL (rm_xs35 i seen)) with E5.
    split; [|split; [exact I | exact I]]. cbn [rm_facts35 f_atoms atoms_ok].
    split; [apply (rm_afact E5 2 (spZ regs - 128)); [exact U5 | lia | change (2 ^ 4) with 16; lia | lia]|].
    split; [apply (rm_afact E5 20 SHADOW_OFF); [exact U5_20 | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    exact I. }
assert (HEI5 : img_env VAL A_LIM E5) by (subst E5; unfold rm_Es; apply Eimg_env).
assert (SHOK5 : sh_ok SEGS (SOff 20 0) [] E5 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_rm_B PA B PST ARx _ LAWS _ RLAW).
(* ---- slots 35 .. 39: the shadow cell of top[i] (0), a1 = top[i], a0 = doc, the call pj_get_str (doc, top[i]) ---- *)
paj_run_tok_x_inv RUN HS5 HJ SHOK5 HPM RM_Bspan.
all: try (rm_awr U5).
clear HG.
rm_reinv HI HS5 HJ HPM HFr U5 HI5. clear HF HFr.
assert (ER5 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E5 n = getr regsL r)
  by (intros n r Hn Hr; exact (rm_Es_reg regsL (rm_xs35 i seen) n r Hn Hr)).
assert (HAE5 : env_agree 32 (Ereg regsL (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) (rm_xs35 i seen))) E5)
  by (split; [intros n Hn; subst E5; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS E5 _ _ regsL _ [3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 22%bv; 23%bv] HS5 HAE5
  ltac:(vm_compute; reflexivity)) as KR5.
prreg HS5 (1%bv : bv 5) R1. prreg HS5 (2%bv : bv 5) R2. prreg HS5 (10%bv : bv 5) R10. prreg HS5 (11%bv : bv 5) R11.
rm_rawreg HS5 (19%bv : bv 5) R19. rm_rawreg HS5 (21%bv : bv 5) R21.
rm_frame_rg HS5 RG5.
lazymatch type of HS5 with st_ok _ _ _ (restrict _ ?msq) => rename msq into ms5 end.
assert (Hseen5 : val_mem SEGS (rdW W2 (ms_mem ms5)) (spZ regs - 128 + 16) 8 seen).
{ pose proof (rm_slot_of_region E5 _ _ 16 (SOff 47 0) RG5 U5 ltac:(cbn [In]; repeat first [left; reflexivity | right]))
    as Hv. cbn [sv_denot] in Hv. rewrite E5_47, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hv by lia. exact Hv. }
clear RG5.
assert (Hsp5 : spZ (ms_regs ms5) = spZ regs - 128)
  by (unfold spZ at 1; rewrite R2, (ER5 2%nat 2%bv), G2 by (lia || reflexivity); apply unsigned_lit_small; lia).
(* ---- the call pj_get_str (doc, top[i]) (slot 39) ---- *)
eapply SRr_bind.
{ eapply (rm_call_inv true W2 E5 _ ms5 ly2 _ _ doc (0x11020 + 32 * Z.of_nat i) (snd (nth i rm_keytab (0, []))) t D
    (AF_rmB + 160) HS5 eq_refl eq_refl HI5 Hsp5).
  - rewrite (KR5 3%bv) by (cbn; tauto). exact G3.
  - rewrite (KR5 4%bv) by (cbn; tauto). exact G4.
  - exact R1.
  - unfold AF_rmB, RMB_SLOT. lia.
  - unfold AF_rmB, RMB_SLOT. reflexivity.
  - vm_compute. reflexivity.
  - unfold s0Z. rewrite (KR5 8%bv) by (cbn; tauto). rewrite G8. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). pose proof rm_entry_stk as (_ & _ & _ & _ & _ & H47' & _ & Htop1 & Htop2).
    destruct i as [|i']; [left; cbn; pose proof (@YM05.alloc_ceiling_lt rc); lia|].
    right; left.
    assert (Hm : (- 8 * Z.of_nat (Datatypes.S i')) mod 2 ^ 64 = 2 ^ 64 - 8 * Z.of_nat (Datatypes.S i'))
      by (symmetry; apply Z.mod_unique with (q := -1); lia).
    rewrite Hm. lia.
  - rewrite R10, (ER5 18%nat 18%bv), G18 by (lia || reflexivity). reflexivity.
  - rewrite R11, E5_46. unfold w64. f_equal. lia.
  - exact (rm_top_key i Hi6).
  - right; left. repeat split. }
cbv beta. intros W3 c3 _ (ly3 & regs3 & mem3 & md3 & k3 & -> & HI3 & HP3 & HKF3 & _).
rewrite R1.
rm_pres HP3 2 (2%bv : bv 5) P2. rm_pres HP3 3 (3%bv : bv 5) P3. rm_pres HP3 4 (4%bv : bv 5) P4.
rm_pres HP3 8 (8%bv : bv 5) P8. rm_pres HP3 9 (9%bv : bv 5) P9. rm_pres HP3 18 (18%bv : bv 5) P18.
rm_pres HP3 19 (19%bv : bv 5) P19. rm_pres HP3 20 (20%bv : bv 5) P20. rm_pres HP3 21 (21%bv : bv 5) P21.
rm_pres HP3 22 (22%bv : bv 5) P22. rm_pres HP3 23 (23%bv : bv 5) P23.
assert (Hseen3 : val_mem SEGS (rdW W3 mem3) (spZ regs - 128 + 16) 8 seen) by (apply HKF3; [lia | cbn; lia | exact Hseen5]).
pose proof HI3 as ((HJ3 & Eab3) & HLd3 & HPM3 & HFR3).
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kpres3 & _).
assert (G3_2 : getr regs3 2 = Z_to_bv 64 (spZ regs - 128)) by (rewrite P2, R2, (ER5 2%nat 2%bv), G2 by (lia || reflexivity); reflexivity).
assert (G3_20 : getr regs3 20 = w64 SHADOW_OFF) by (rewrite P20, (KR5 20%bv) by (cbn; tauto); exact G20).
set (E4 := rm_Es regs3 [seen]).
assert (E4_45 : ew E4 45 = Z_to_bv 64 seen) by exact (rm_Es_x regs3 [seen] 0 ltac:(cbn; lia) ltac:(lia)).
assert (ER4 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E4 n = getr regs3 r)
  by (intros n r Hn Hr; exact (rm_Es_reg regs3 [seen] n r Hn Hr)).
assert (U4 : bv_unsigned (ew E4 2) = spZ regs - 128)
  by (rewrite (ER4 2%nat 2%bv), G3_2 by (lia || reflexivity); apply unsigned_lit_small; lia).
assert (U4_20 : bv_unsigned (ew E4 20) = SHADOW_OFF)
  by (rewrite (ER4 20%nat 20%bv), G3_20 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (CK4 : YP09.chunk_ok SEGS E4 (rdW W3 mem3) (spZ regs - 128) (YP09.mkChunk 16 (CVal 8 (SOff 45 0)))).
{ apply (chunk_ok_val SEGS E4 _ (spZ regs - 128) 16 8 (SOff 45 0) seen);
  [cbn [sv_denot]; rewrite E4_45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hseen3]. }
assert (HS4 : st_ok_pi SEGS VAL E4 (mkSS (AF_rmB + 160) sr_atoms [rm_frame_region [YP09.mkChunk 16 (CVal 8 (SOff 45 0))]]
    None rm_facts35) (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_rmB + 160))) mem3 (seg_rom SEGS)))).
{ apply rm_seat; [exact G3_2 | exact HFR3 | intros a Ha; apply Kpres3; rewrite FS; lia | constructor; [exact CK4 | constructor]
  | vm_compute; reflexivity | constructor | |].
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - change (rm_Es regs3 [seen]) with E4.
    split; [|split; [exact I | exact I]]. cbn [rm_facts35 f_atoms atoms_ok].
    split; [apply (rm_afact E4 2 (spZ regs - 128)); [exact U4 | lia | change (2 ^ 4) with 16; lia | lia]|].
    split; [apply (rm_afact E4 20 SHADOW_OFF); [exact U4_20 | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    exact I. }
assert (HEI4 : img_env VAL A_LIM E4) by (subst E4; unfold rm_Es; apply Eimg_env).
assert (SHOK4 : sh_ok SEGS (SOff 20 0) [] E4 (mrestrict (w_H W3) mem3)) by constructor.
change (Z_to_bv 64 (BASE + 3880)) with (Z_to_bv 64 (BASE + (AF_rmB + 160))).
(* ---- slots 40 .. 47: the counter += (result <> 0), s0 -= 8, s5 += 1, s3 += 8, bne s0 s6 ---- *)
paj_run_tok_x_inv RUN HS4 HJ3 SHOK4 HPM3 RM_Bspan; [rm_awr U4|].
clear HG.
pose (BR := paj_branch (PI := PA)).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_rm_B PA B PST ARx _ LAWS _ RLAW).
rm_reinv HI3 HS4 HJ3 HPM3 HFr U4 HI4.
clear HF HFr.
assert (EW8 : ew E4 8 = w64 (- 8 * Z.of_nat i))
  by (rewrite (ER4 8%nat 8%bv), P8, (KR5 8%bv) by (cbn; tauto || lia || reflexivity); exact G8).
assert (EW19 : ew E4 19 = w64 (VAL (A_OBJ 3) + 8 * Z.of_nat i)).
{ rewrite (ER4 19%nat 19%bv), P19, R19 by (lia || reflexivity). rewrite (rm_w64_off E5 45 _ 0 E5_45). f_equal. lia. }
assert (EW21 : ew E4 21 = w64 cell).
{ rewrite (ER4 21%nat 21%bv), P21, R21 by (lia || reflexivity). rewrite (rm_w64_off E5 48 _ 0 E5_48). f_equal. lia. }
assert (EW22 : ew E4 22 = w64 (-48))
  by (rewrite (ER4 22%nat 22%bv), P22, (KR5 22%bv) by (cbn; tauto || lia || reflexivity); exact G22).
psrr_branch_tok RUN BR HS4 SHOK4 RM_Bspan.
all: rewrite branch_ne_U in Hc; unfold U in Hc;
  rewrite (rm_w64_off E4 8 _ (-8) EW8), (rm_w64_off E4 22 _ 0 EW22) in Hc.
- (* taken: i + 1 < 6, back to the loop head with i + 1 *)
  assert (Hlt : (i < 5)%nat) by (destruct i as [|[|[|[|[|[|i']]]]]]; try lia; vm_compute in Hc; discriminate Hc).
  paj_run_to_tok_x_inv RUNTO HS4 HJ3 SHOK4 HPM3 RM_Bspan (AF_rmB + 140); [rm_awr U4|].
  clear HG.
  rm_reinv HI4 HS4 HJ3 HPM3 HFr U4 HI6. clear HF HFr.
  rm_rawreg HS4 (8%bv : bv 5) N8. rm_rawreg HS4 (19%bv : bv 5) N19. rm_rawreg HS4 (21%bv : bv 5) N21.
  assert (HAE4 : env_agree 32 (Ereg regs3 (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seen])) E4)
    by (split; [intros n Hn; subst E4; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E4 _ _ regs3 _ [2%bv; 3%bv; 4%bv; 9%bv; 18%bv; 20%bv; 22%bv; 23%bv] HS4 HAE4
    ltac:(vm_compute; reflexivity)) as KR6.
  rm_frame_rg HS4 RG6.
  lazymatch type of RG6 with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
    pose proof (rm_slot_of_region E4 _ _ 16 e16 RG6 U4 ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hseen6;
    set (seen6 := bv_unsigned (sv_denot E4 e16)) in Hseen6 end.
  clear RG6.
  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into ms6 end.
  pmkst HS4.
  eapply (IH Hlt W3 (ms_regs ms6) (ms_mem ms6) _ _ _ z1 z2 seen6).
  split; [exact HI6|]. split; [exact Hseen6|]. split; [apply bv_unsigned_in_range|].
  split; [rewrite (KR6 2%bv) by (cbn; tauto); exact G3_2|].
  split; [rewrite (KR6 3%bv), P3, (KR5 3%bv) by (cbn; tauto); exact G3|].
  split; [rewrite (KR6 4%bv), P4, (KR5 4%bv) by (cbn; tauto); exact G4|].
  split; [rewrite N8, (rm_w64_off E4 8 _ (-8) EW8); f_equal; lia|].
  split; [rewrite (KR6 9%bv), P9, (KR5 9%bv) by (cbn; tauto); exact G9|].
  split; [rewrite (KR6 18%bv), P18, (KR5 18%bv) by (cbn; tauto); exact G18|].
  split; [rewrite N19, (rm_w64_off E4 19 _ 8 EW19); f_equal; lia|].
  split; [rewrite (KR6 20%bv) by (cbn; tauto); exact G3_20|].
  split; [rewrite N21, (rm_w64_off E4 21 _ 1 EW21); f_equal; subst cell; lia|].
  split; [rewrite (KR6 22%bv), P22, (KR5 22%bv) by (cbn; tauto); exact G22|].
  split; [rewrite (KR6 23%bv), P23, (KR5 23%bv) by (cbn; tauto); exact G23|].
  split; [exact Hz1|]. split; [exact Hz2|]. split; [exact Rz1 | exact Rz2].
- (* not taken: i = 5; slot 8 = z2, the call pj_get (doc, "plugin") *)
  assert (Hi5e : i = 5%nat) by (destruct i as [|[|[|[|[|[|i']]]]]]; try reflexivity; try lia; vm_compute in Hc; discriminate Hc).
  subst i.
  paj_run_tok_x_inv RUN HS4 HJ3 SHOK4 HPM3 RM_Bspan; [rm_awr U4|].
  clear HG.
  rm_reinv HI4 HS4 HJ3 HPM3 HFr U4 HI7. clear HF HFr.
  assert (HAE4 : env_agree 32 (Ereg regs3 (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [seen])) E4)
    by (split; [intros n Hn; subst E4; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof (regs_kept_of_st_ok SEGS E4 _ _ regs3 _ [2%bv; 3%bv; 4%bv; 9%bv; 18%bv; 20%bv] HS4 HAE4
    ltac:(vm_compute; reflexivity)) as KR7.
  prreg HS4 (1%bv : bv 5) R1'. prreg HS4 (10%bv : bv 5) R10'. prreg HS4 (11%bv : bv 5) R11'.
  rm_rawreg HS4 (8%bv : bv 5) N8.
  assert (EW23 : ew E4 23 = w64 z2)
    by (rewrite (ER4 23%nat 23%bv), P23, (KR5 23%bv) by (cbn; tauto || lia || reflexivity); exact G23).
  assert (E4_243 : ew E4 243 = Z_to_bv 64 (VAL (A_OBJ 2)))
    by (subst E4; unfold rm_Es; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  rm_frame_rg HS4 RG7.
  pose proof (rm_slot_of_region E4 _ _ 8 (SOff 23 0) RG7 U4 ltac:(cbn [In]; repeat first [left; reflexivity | right]))
    as Hz2s.
  rewrite (rm_w64_off E4 23 z2 0 EW23) in Hz2s. unfold w64 in Hz2s. rewrite Z.add_0_r, unsigned_lit_small in Hz2s by lia.
  lazymatch type of RG7 with context [YP09.mkChunk 16 (CVal 8 ?e16)] =>
    pose proof (rm_slot_of_region E4 _ _ 16 e16 RG7 U4 ltac:(cbn [In]; repeat first [left; reflexivity | right])) as Hseen7;
    set (seen7 := bv_unsigned (sv_denot E4 e16)) in Hseen7 end.
  clear RG7.
  lazymatch type of HS4 with st_ok _ _ _ (restrict _ ?msq) => rename msq into ms7 end.
  assert (Hsp7 : spZ (ms_regs ms7) = spZ regs - 128)
    by (unfold spZ at 1; rewrite (KR7 2%bv) by (cbn; tauto); rewrite G3_2; apply unsigned_lit_small; lia).
  (* ---- the call pj_get (doc, "plugin") (slot 52) ---- *)
  eapply SRr_bind.
  { eapply (rm_call_inv false W3 E4 _ ms7 ly3 _ _ doc 0x11120 [112; 108; 117; 103; 105; 110] t D (AF_rmB + 212)
      HS4 eq_refl eq_refl HI7 Hsp7).
    - rewrite (KR7 3%bv), P3, (KR5 3%bv) by (cbn; tauto). exact G3.
    - rewrite (KR7 4%bv), P4, (KR5 4%bv) by (cbn; tauto). exact G4.
    - exact R1'.
    - unfold AF_rmB, RMB_SLOT. lia.
    - unfold AF_rmB, RMB_SLOT. reflexivity.
    - vm_compute. reflexivity.
    - right; left. unfold s0Z. rewrite N8, (rm_w64_off E4 8 _ (-8) EW8). unfold w64. rewrite Z_to_bv_unsigned.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      pose proof rm_entry_stk as (_ & _ & _ & _ & _ & H47' & _ & Htop1 & Htop2). cbn [Z.of_nat Pos.of_succ_nat]. lia.
    - rewrite R10', (ER4 18%nat 18%bv), P18, (KR5 18%bv), G18 by (cbn; tauto || lia || reflexivity). reflexivity.
    - rewrite R11', E4_243, unsigned_lit_small by lia. reflexivity.
    - cbn [rm_keytab In]. repeat first [left; reflexivity | right].
    - right; left. repeat split. }
  cbv beta. intros W8 c8 _ (ly8 & regs8 & mem8 & md8 & k8 & -> & HI8 & HP8 & HKF8 & HRES8).
  rewrite R1'.
  destruct HRES8 as [(Hd0 & _) | (_ & z4 & Hz4 & Hres4)]; [pose proof Hrs as (Hd4 & _); lia|].
  cbn [rm_kres] in Hres4.
  pose proof (rm_get_sub ly8 W8 mem8 md8 k8 _ z4 (proj1 HI8) Hres4) as Hz4s.
  rm_pres HP8 2 (2%bv : bv 5) Q2. rm_pres HP8 3 (3%bv : bv 5) Q3. rm_pres HP8 4 (4%bv : bv 5) Q4.
  rm_pres HP8 8 (8%bv : bv 5) Q8. rm_pres HP8 9 (9%bv : bv 5) Q9. rm_pres HP8 18 (18%bv : bv 5) Q18.
  rm_pres HP8 20 (20%bv : bv 5) Q20.
  change (Z_to_bv 64 (BASE + 3932)) with (Z_to_bv 64 (BASE + (AF_rmB + 212))).
  apply (rm_after_c4 W8 regs8 mem8 md8 ly8 k8 z1 z2 z4 seen7).
  split; [exact HI8|].
  split; [apply HKF8; [lia | cbn; lia | exact Hseen7]|]. split; [apply bv_unsigned_in_range|].
  split; [apply HKF8; [lia | cbn; lia | exact Hz2s]|].
  split; [rewrite Q2, (KR7 2%bv) by (cbn; tauto); exact G3_2|].
  split; [rewrite Q3, (KR7 3%bv), P3, (KR5 3%bv) by (cbn; tauto); exact G3|].
  split; [rewrite Q4, (KR7 4%bv), P4, (KR5 4%bv) by (cbn; tauto); exact G4|].
  split; [rewrite Q8, N8, (rm_w64_off E4 8 _ (-8) EW8); f_equal; lia|].
  split; [rewrite Q9, (KR7 9%bv), P9, (KR5 9%bv) by (cbn; tauto); exact G9|].
  split; [rewrite Q18, (KR7 18%bv), P18, (KR5 18%bv) by (cbn; tauto); exact G18|].
  split; [rewrite Q20, (KR7 20%bv) by (cbn; tauto); exact G3_20|].
  split; [exact Hz4|].
  split; [exact Hz1|]. split; [exact Hz2|]. split; [exact Hz4s|].
  split; [exact Rz1|]. split; [exact Rz2|].
  destruct Hz4s as [-> | (v4 & D4 & Hs4)]; [lia|]. pose proof (rm_sub_range z4 v4 D4 Hs4). lia.
Qed.

Lemma rm_top_loop : forall i, (i <= 5)%nat -> rm_topP i.
Proof.
intros i Hi. remember (5 - i)%nat as n eqn:En. revert i Hi En. induction n as [|n IHn]; intros i Hi En.
- apply rm_top_iter; [lia|]. intros Hlt. lia.
- apply rm_top_iter; [lia|]. intros Hlt. apply IHn; lia.
Qed.

Lemma rm_main : SRr SEGS W (cfg_at SEGS (SIGMA AS_read_members) regs mem md) rm_goal.
Proof.
pose proof HFPRE as (HPRE & HROD & HTOP & HRAZ & HFRM).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof rm_stks as (FS & FS1 & FS2).
pose proof rm_sp_bounds as (SB1 & SB2 & SB3).
destruct rm_entry_seat as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
remember (rm_E0 regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rm_E0; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; unfold rm_E0; apply Eimg_low; exact Hn).
assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); reflexivity).
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as RLAW.
assert (HPM : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem) by (intros h; exact h).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_rm_B PA B PST ARx _ LAWS _ RLAW).
unfold cfg_at. rewrite rm_pa_ent. change (w64 (BASE + AF_rmB)) with (Z_to_bv 64 (BASE + AF_rmB)).
(* ---- slots 0 .. 21: the frame, the thirteen saves, s4 = the shadow base, s2 = doc, the call pj_get (doc, "params") ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM RM_Bspan; [rm_awr Usp|].
clear HG.
(* the call state: the frame's thirteen words written, every other byte as at entry *)
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. unfold aview, mbyte. rewrite (rm_mr_keep E (ss_mem ss_rm0) _ _ a HFr); [reflexivity | | exact Ha].
  intros (r & Hin & Hr). vm_compute in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite Usp in Hr|..]; lia. }
clear HF HFr.
lazymatch type of HS with st_ok _ _ ?ss _ => pose proof (rm_region_nth SEGS E ss _ 0 _ HS eq_refl) as RG0 end.
cbn [ms_mem restrict] in RG0.
assert (HFR1 : rm_frame W (ms_mem ms)).
{ unfold rm_frame, rm_saves. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: lazymatch goal with |- val_mem _ _ (spZ regs - 128 + ?off) 8 (bv_unsigned (getr regs ?r)) =>
    let od := eval vm_compute in (off - 128) in
    let q := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    replace (spZ regs - 128 + off) with (spZ regs + od) by lia;
    apply (rm_field_of_region SEGS E _ 2 (spZ regs) _ (-128) 0 (-128) 0 od 8 (SOff q 0) (bv_unsigned (getr regs r)) RG0 Usp);
    [ cbn [In]; repeat first [left; reflexivity | right]
    | cbn [sv_denot]; rewrite (ER q r) by (lia || reflexivity); rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 _)
    | cbn; lia ] end. }
clear RG0.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
prreg HS (18%bv : bv 5) R18. prreg HS (20%bv : bv 5) R20.
assert (E243 : ew E 243 = Z_to_bv 64 (VAL (A_OBJ 2)))
  by (subst E; unfold rm_E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
pose proof (pa_val_range (A_OBJ 2)) as RV2. pose proof rm_pa_o2 as HO2. unfold IMG_LO_B in HO2.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 128) by (unfold spZ at 1; rewrite R2, Usp; apply unsigned_lit_small; lia).
assert (HLED1 : prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W (ms_mem ms) Lam peak cnt fail ran most own)
  by (apply (rm_led_keep ly W mem (ms_mem ms) HLED); intros a Ha; apply KM1; lia).
assert (KL1 : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KM1; lia).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_rm_B PA B PST ARx _ LAWS _ RLAW).
(* ---- the call pj_get (doc, "params") (slot 21) ---- *)
eapply SRr_bind.
{ eapply (rm_call_inv false W E _ ms ly _ _ doc 0x110e0 [112; 97; 114; 97; 109; 115] t D 3808 HS eq_refl eq_refl).
  - split; [split; [exact HJ | reflexivity]|]. split; [exact HLED1|]. split; [exact HPM|]. exact HFR1.
  - exact Hsp1.
  - rewrite R3. apply (ER 3%nat 3%bv); [lia | reflexivity].
  - rewrite R4. apply (ER 4%nat 4%bv); [lia | reflexivity].
  - exact R1.
  - lia.
  - reflexivity.
  - vm_compute. reflexivity.
  - right; right. rewrite R8. apply (ER 8%nat 8%bv); [lia | reflexivity].
  - rewrite R10, (ER 10%nat 10%bv) by (lia || reflexivity). exact H10.
  - rewrite R11, E243, unsigned_lit_small by lia. reflexivity.
  - cbn [rm_keytab In]. repeat first [left; reflexivity | right].
  - right; left. repeat split. }
cbv beta. intros W3 c3 _ (ly3 & regs3 & mem3 & md3 & k3 & -> & HI3 & HP3 & HKF3 & HRES3).
rewrite R1.
rm_pres HP3 2 (2%bv : bv 5) P2. rm_pres HP3 3 (3%bv : bv 5) P3. rm_pres HP3 4 (4%bv : bv 5) P4.
rm_pres HP3 8 (8%bv : bv 5) P8. rm_pres HP3 18 (18%bv : bv 5) P18. rm_pres HP3 20 (20%bv : bv 5) P20.
destruct HRES3 as [(Hd0 & _) | (_ & z1 & Hz1 & Hres1)]; [pose proof Hrs as (Hd4 & _); lia|].
cbn [rm_kres] in Hres1.
pose proof (rm_get_sub ly3 W3 mem3 md3 k3 _ z1 (proj1 HI3) Hres1) as Hz1s.
pose proof HI3 as ((HJ3 & Eab3) & HLd3 & HPM3 & HFR3).
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kpres3 & _).
assert (G3_2 : getr regs3 2 = Z_to_bv 64 (spZ regs - 128)) by (rewrite P2, R2, Usp; reflexivity).
assert (G3_3 : getr regs3 3 = getr regs 3) by (rewrite P3, R3; apply (ER 3%nat 3%bv); [lia | reflexivity]).
assert (G3_4 : getr regs3 4 = getr regs 4) by (rewrite P4, R4; apply (ER 4%nat 4%bv); [lia | reflexivity]).
assert (G3_8 : getr regs3 8 = getr regs 8) by (rewrite P8, R8; apply (ER 8%nat 8%bv); [lia | reflexivity]).
assert (G3_18 : getr regs3 18 = w64 doc) by (rewrite P18, R18, (ER 10%nat 10%bv) by (lia || reflexivity); exact H10).
assert (G3_20 : getr regs3 20 = w64 SHADOW_OFF) by (rewrite P20, R20, E32; reflexivity).
set (EA1 := rm_Es regs3 []).
assert (ERA1 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EA1 n = getr regs3 r)
  by (intros n r Hn Hr; exact (rm_Es_reg regs3 [] n r Hn Hr)).
assert (UspA1 : bv_unsigned (ew EA1 2) = spZ regs - 128)
  by (rewrite (ERA1 2%nat 2%bv), G3_2 by (lia || reflexivity); apply unsigned_lit_small; lia).
assert (UA1_20 : bv_unsigned (ew EA1 20) = SHADOW_OFF)
  by (rewrite (ERA1 20%nat 20%bv), G3_20 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HSA1 : st_ok_pi SEGS VAL EA1 (mkSS (AF_rmB + 88) sr_atoms [rm_frame_region []] None rm_facts35)
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_rmB + 88))) mem3 (seg_rom SEGS)))).
{ apply rm_seat; [exact G3_2 | exact HFR3 | intros a Ha; apply Kpres3; rewrite FS; lia | constructor
  | vm_compute; reflexivity | constructor | cbn [pairwise_disjoint all_disjoint]; exact (conj I I) |].
  change (rm_Es regs3 []) with EA1.
  split; [|split; [exact I | exact I]]. cbn [rm_facts35 f_atoms atoms_ok].
  split; [apply (rm_afact EA1 2 (spZ regs - 128)); [exact UspA1 | lia | change (2 ^ 4) with 16; lia | lia]|].
  split; [apply (rm_afact EA1 20 SHADOW_OFF); [exact UA1_20 | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  exact I. }
assert (HEIA1 : img_env VAL A_LIM EA1) by (subst EA1; unfold rm_Es; apply Eimg_env).
assert (SHOKA1 : sh_ok SEGS (SOff 20 0) [] EA1 (mrestrict (w_H W3) mem3)) by constructor.
change (Z_to_bv 64 (BASE + 3808)) with (Z_to_bv 64 (BASE + (AF_rmB + 88))).
(* ---- slots 22 .. 26: s1 = the params member, a1 = "state", a0 = doc, the call pj_get (doc, "state") ---- *)
paj_run_tok_x_inv RUN HSA1 HJ3 SHOKA1 HPM3 RM_Bspan; [rm_awr UspA1|].
clear HG.
rm_reinv HI3 HSA1 HJ3 HPM3 HFr UspA1 HI4. clear HF HFr.
assert (HAEA1 : env_agree 32 (Ereg regs3 (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [])) EA1)
  by (split; [intros n Hn; subst EA1; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS EA1 _ _ regs3 _ [2%bv; 3%bv; 4%bv; 8%bv; 18%bv; 20%bv] HSA1 HAEA1
  ltac:(vm_compute; reflexivity)) as KRb.
prreg HSA1 (1%bv : bv 5) R1b. prreg HSA1 (9%bv : bv 5) R9b. prreg HSA1 (10%bv : bv 5) R10b. prreg HSA1 (11%bv : bv 5) R11b.
assert (EA1_243 : ew EA1 243 = Z_to_bv 64 (VAL (A_OBJ 2)))
  by (subst EA1; unfold rm_Es; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
lazymatch type of HSA1 with st_ok _ _ _ (restrict _ ?msq) => rename msq into ms2 end.
assert (Hsp2 : spZ (ms_regs ms2) = spZ regs - 128)
  by (unfold spZ at 1; rewrite (KRb 2%bv) by (cbn; tauto); rewrite G3_2; apply unsigned_lit_small; lia).
(* ---- the call pj_get (doc, "state") (slot 26) ---- *)
eapply SRr_bind.
{ eapply (rm_call_inv false W3 EA1 _ ms2 ly3 _ _ doc 0x11100 [115; 116; 97; 116; 101] t D 3828 HSA1 eq_refl eq_refl HI4 Hsp2).
  - rewrite (KRb 3%bv) by (cbn; tauto). exact G3_3.
  - rewrite (KRb 4%bv) by (cbn; tauto). exact G3_4.
  - exact R1b.
  - lia.
  - reflexivity.
  - vm_compute. reflexivity.
  - right; right. rewrite (KRb 8%bv) by (cbn; tauto). exact G3_8.
  - rewrite R10b, (ERA1 18%nat 18%bv) by (lia || reflexivity). exact G3_18.
  - rewrite R11b, EA1_243, unsigned_lit_small by lia. reflexivity.
  - cbn [rm_keytab In]. repeat first [left; reflexivity | right].
  - right; left. repeat split. }
cbv beta. intros W4 c4 _ (ly4 & regs4 & mem4 & md4 & k4 & -> & HI5 & HP5 & HKF5 & HRES5).
rewrite R1b.
destruct HRES5 as [(Hd0 & _) | (_ & z2 & Hz2 & Hres2)]; [pose proof Hrs as (Hd4 & _); lia|].
cbn [rm_kres] in Hres2.
pose proof (rm_get_sub ly4 W4 mem4 md4 k4 _ z2 (proj1 HI5) Hres2) as Hz2s.
rm_pres HP5 2 (2%bv : bv 5) Q2. rm_pres HP5 3 (3%bv : bv 5) Q3. rm_pres HP5 4 (4%bv : bv 5) Q4.
rm_pres HP5 9 (9%bv : bv 5) Q9. rm_pres HP5 18 (18%bv : bv 5) Q18. rm_pres HP5 20 (20%bv : bv 5) Q20.
pose proof HI5 as ((HJ5 & Eab5) & HLd5 & HPM5 & HFR5).
pose proof HJ5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kpres5 & _).
assert (G4_2 : getr regs4 2 = Z_to_bv 64 (spZ regs - 128)) by (rewrite Q2, (KRb 2%bv) by (cbn; tauto); exact G3_2).
assert (G4_3 : getr regs4 3 = getr regs 3) by (rewrite Q3, (KRb 3%bv) by (cbn; tauto); exact G3_3).
assert (G4_4 : getr regs4 4 = getr regs 4) by (rewrite Q4, (KRb 4%bv) by (cbn; tauto); exact G3_4).
assert (G4_9 : getr regs4 9 = w64 z1) by (rewrite Q9, R9b, (ERA1 10%nat 10%bv) by (lia || reflexivity); exact Hz1).
assert (G4_18 : getr regs4 18 = w64 doc) by (rewrite Q18, (KRb 18%bv) by (cbn; tauto); exact G3_18).
assert (G4_20 : getr regs4 20 = w64 SHADOW_OFF) by (rewrite Q20, (KRb 20%bv) by (cbn; tauto); exact G3_20).
set (EA2 := rm_Es regs4 []).
assert (ERA2 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EA2 n = getr regs4 r)
  by (intros n r Hn Hr; exact (rm_Es_reg regs4 [] n r Hn Hr)).
assert (UspA2 : bv_unsigned (ew EA2 2) = spZ regs - 128)
  by (rewrite (ERA2 2%nat 2%bv), G4_2 by (lia || reflexivity); apply unsigned_lit_small; lia).
assert (UA2_20 : bv_unsigned (ew EA2 20) = SHADOW_OFF)
  by (rewrite (ERA2 20%nat 20%bv), G4_20 by (lia || reflexivity); unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HSA2 : st_ok_pi SEGS VAL EA2 (mkSS (AF_rmB + 108) sr_atoms [rm_frame_region []] None rm_facts35)
  (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + (AF_rmB + 108))) mem4 (seg_rom SEGS)))).
{ apply rm_seat; [exact G4_2 | exact HFR5 | intros a Ha; apply Kpres5; rewrite FS; lia | constructor
  | vm_compute; reflexivity | constructor | cbn [pairwise_disjoint all_disjoint]; exact (conj I I) |].
  change (rm_Es regs4 []) with EA2.
  split; [|split; [exact I | exact I]]. cbn [rm_facts35 f_atoms atoms_ok].
  split; [apply (rm_afact EA2 2 (spZ regs - 128)); [exact UspA2 | lia | change (2 ^ 4) with 16; lia | lia]|].
  split; [apply (rm_afact EA2 20 SHADOW_OFF); [exact UA2_20 | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  exact I. }
assert (HEIA2 : img_env VAL A_LIM EA2) by (subst EA2; unfold rm_Es; apply Eimg_env).
assert (SHOKA2 : sh_ok SEGS (SOff 20 0) [] EA2 (mrestrict (w_H W4) mem4)) by constructor.
change (Z_to_bv 64 (BASE + 3828)) with (Z_to_bv 64 (BASE + (AF_rmB + 108))).
(* ---- slots 27 .. 34: s7 = the state member, s0 = 0, the counter = 0, s3 = top, s5 = its shadow cell, s6 = -48 ---- *)
paj_run_to_tok_x_inv RUNTO HSA2 HJ5 SHOKA2 HPM5 RM_Bspan (AF_rmB + 140); [rm_awr UspA2|].
clear HG.
rm_reinv HI5 HSA2 HJ5 HPM5 HFr UspA2 HI6. clear HF HFr.
assert (HAEA2 : env_agree 32 (Ereg regs4 (map (fun sr => getr regs (snd sr)) rm_saves ++ map (Z_to_bv 64) [])) EA2)
  by (split; [intros n Hn; subst EA2; unfold rm_Es; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok_pi (PI := PA) EA2 _ _ regs4 _ [2%bv; 3%bv; 4%bv; 9%bv; 18%bv; 20%bv] HSA2 HAEA2
  ltac:(vm_compute; reflexivity)) as KRc.
rm_rawreg HSA2 (8%bv : bv 5) N8. rm_rawreg HSA2 (19%bv : bv 5) N19. rm_rawreg HSA2 (21%bv : bv 5) N21.
rm_rawreg HSA2 (22%bv : bv 5) N22. rm_rawreg HSA2 (23%bv : bv 5) N23.
assert (EA2_244 : ew EA2 (A_OBJ 3) = w64 (VAL (A_OBJ 3)))
  by (subst EA2; unfold rm_Es; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 3)) as RV3.
pose proof RM_IMG as (_ & (Ht1 & Ht2 & Ht3) & _).
assert (Htlow : VAL (A_OBJ 3) + 48 <= kLowMemEnd).
{ destruct (Ht3 (VAL (A_OBJ 3) + 47) ltac:(lia)) as (Hro & _).
  pose proof (@pa_segs_low _ _ PA _ (rm_ro_img _ Hro)) as HL'. unfold kLowMemEnd in *. lia. }
unfold kLowMemEnd in Htlow.
rm_frame_rg HSA2 RGc.
pose proof (rm_slot_of_region EA2 _ _ 16 (SLit 0) RGc UspA2 ltac:(cbn [In]; repeat first [left; reflexivity | right]))
  as Hseen0.
change (bv_unsigned (sv_denot EA2 (SLit 0))) with (bv_unsigned (Z_to_bv 64 0)) in Hseen0.
rewrite unsigned_lit_small in Hseen0 by lia.
clear RGc.
lazymatch type of HSA2 with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into ms3 end.
pmkst HSA2.
assert (Rz1 : 0 <= z1 < 2 ^ 64)
  by (destruct Hz1s as [-> | (v1 & D1 & Hs1)]; [lia | pose proof (rm_sub_range z1 v1 D1 Hs1); lia]).
assert (Rz2 : 0 <= z2 < 2 ^ 64)
  by (destruct Hz2s as [-> | (v2 & D2 & Hs2)]; [lia | pose proof (rm_sub_range z2 v2 D2 Hs2); lia]).
eapply (rm_top_loop 0 ltac:(lia) W4 (ms_regs ms3) (ms_mem ms3) _ _ _ z1 z2 0).
split; [exact HI6|]. split; [exact Hseen0|]. split; [lia|].
split; [rewrite (KRc 2%bv) by (cbn; tauto); exact G4_2|].
split; [rewrite (KRc 3%bv) by (cbn; tauto); exact G4_3|].
split; [rewrite (KRc 4%bv) by (cbn; tauto); exact G4_4|].
split; [rewrite N8; reflexivity|].
split; [rewrite (KRc 9%bv) by (cbn; tauto); exact G4_9|].
split; [rewrite (KRc 18%bv) by (cbn; tauto); exact G4_18|].
split; [change 244%nat with (A_OBJ 3) in N19; rewrite N19, (rm_w64_off EA2 (A_OBJ 3) _ 0 EA2_244); f_equal; lia|].
split; [rewrite (KRc 20%bv) by (cbn; tauto); exact G4_20|].
split; [rewrite N21; apply (rm_U_reg EA2 (rm_shx 20 (A_OBJ 3))); [reflexivity | |];
  [apply rm_shx_U; [exact UA2_20 | rewrite EA2_244; unfold w64; rewrite unsigned_lit_small by lia; cbn [Z.of_nat]; lia | lia]
  | pose proof (Z.div_pos (VAL (A_OBJ 3)) 8 ltac:(lia) ltac:(lia));
    assert (VAL (A_OBJ 3) / 8 < 2 ^ 28) by (apply Z.div_lt_upper_bound; lia); unfold SHADOW_OFF; lia]|].
split; [rewrite N22; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite N23, (rm_w64_off EA2 10 z2 0) by (rewrite (ERA2 10%nat 10%bv) by (lia || reflexivity); exact Hz2);
  f_equal; lia|].
split; [exact Hz1s|]. split; [exact Hz2s|]. split; [exact Rz1 | exact Rz2].
Qed.

End w.

Theorem read_members_holds : tread_members_specX (cp := CP) (PI := prh_img_B) (PA := PA) B ARx SK.
Proof.
unfold tread_members_specX.
intros ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own HFPRE H10 Hnode Hrs HLED.
exact (rm_main ly S Hp W regs mem md ch doc t D Lam peak cnt fail ran most own HFPRE H10 Hnode Hrs HLED).
Qed.

End f.
End d.
