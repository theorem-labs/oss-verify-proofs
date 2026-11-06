(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_zone3.v (commit 4d286b2e618d, file sha256 bb641dce35dc) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 11 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, row img-zone3-B of a Theorem Labs lane's internal file REPLY-IMG-ROWS.md, for a Theorem Labs lane's cf layer at
   plugin-hostd/fuzz_reply; merger ReallocPrimary.CfW, lane W).
   rule 24: no function proved (kind: image rows; closed computations at reply's image B, fuzz_reply.asan-ubsan, pin
   10ffb5f9202a).  Reuse search: proof-index ZONE3 CONST_KEEP_S CONST_NOT_JUNK AREAS_DISJ snull_junk
   const_cells_CZS zone3_intro (2026-10-30 04:5xZ, index built 04:38:19Z): the four facts are only the layer's own
   Hypotheses; const_cells_CZS (cgif AGif5.v:336) has ports for cgif, fuzz_preset and fuzz_state and none for reply;
   zone3_intro is reply's own B/YF0x.v:66.

   Statement text of record: the cf layer's YGcfInstSec.v on 8aea1d52068 (ZONE3 :377,
   CONST_KEEP_S :383, snull_junk :740, CONST_NOT_JUNK :748, AREAS_DISJ :752), the same text as at 4c2fd365d8e (:365-366,
   :371-376, :717-721, :725-727, :729).  Each Lemma below states the layer's Hypothesis VERBATIM at reply's instances:
   the image class ImgBase.AImg at AImg_cgif (B/AGif2cgif.v:24), the secondary class ImgBaseAGS.AImgS at
   AImgS_cgif (B/AGif4cgif.v:26) and the cf parameters at CfParams_preset (A/CfParamsPreset.v, the one record of both
   images).  In the three
   facts that name the layer's Section variable B, B and its symbol hypothesis TS : im_syms B are the lemma's first two
   arguments; ZONE3 does not name B, so zone3_B takes neither.  The layer's
   Definition snull_junk is not in reply's tree, so const_not_junk_B states its body unfolded (YGcfInstSec.v:740-744 at
   8aea1d52068), with the layer's B as the lemma's B.  A consumer closes the layer's row with `exact` once the layer is
   on reply.  No Definition of the layer is copied here.
   - ZONE3 (ims_zone3 = zone3 at AImgS_cgif): reply's own zone3_intro.
   - AREAS_DISJ: the eleven areas of asyms_areas at image B.  TfibSyms pins seven of the addresses; the other four
     (the shadow cell, the use-after-return cell and their two GOT cells) are read from asyms_ok's const law over
     Tfib_const: each is the address of the only const cell of its width and value (num_addrs, by computation).
   - CONST_KEEP_S: every byte of every const cell of Tfib_const lies in AGif4.CZS at TFIB_INST, except the mutex's two
     pad cells, whose bytes are 0 (cgif's AGif5.const_cells_CZS, here by computation over Tfib_const_abs and
     Tfib_const_shadow and by cases over Tfib_const_sym); CZS bytes keep their view by the memory premise, pad bytes by
     the pad premise.
   - CONST_NOT_JUNK: no byte of a const cell is in snull_junk: the abs and shadow cells lie in image or shadow pieces
     that miss the instance's junk windows and the out-of-memory byte (by computation), the symbolic cells are in the
     thread, ctx and D objects or at fixed image addresses, and the thread object misses the image and the shadow
     (layout_ok, img_cover).  The by_size_log word lies in [inst + 296, inst + 408) (bsl_bounds, the layer's own lemma,
     YGcfInstSec.v at 8aea1d52068, with its msv_facts, restated over reply's ImgBaseAGS, which has the same text).
   - The one name check of the internal file REPLY-IMG-ROWS.md:74 for this row: CONST_KEEP_S and the layer's dep_keep_img
     (YGcfInstDepot.v:154) are NOT the same text: dep_keep_img keeps CLdepot.depot_mem_ok as well, over any KEEP set,
     with NoDup / incl premises on the depot list and no mutex-pad premise.  So CONST_KEEP_S is stated here on its own. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAGS. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AGif4. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif4cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGjm.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Generic helpers (no image).                                                                                      *)

(* The addresses of the cells of width [w] and value [v] at a numeral address, as a list (a computation). *)
Definition num_addrs (w : nat) (v : Z) (l : list acell) : list Z :=
  flat_map (fun c => match c with
    | ACell (ANum a) w' (AV (ANum v')) => if Nat.eqb w w' && Z.eqb v v' then [a] else []
    | _ => [] end) l.
Lemma num_addrs_in : forall w v a l, In (ACell (ANum a) w (AV (ANum v))) l -> In a (num_addrs w v l).
Proof.
intros w v a l H. unfold num_addrs. apply in_flat_map. exists (ACell (ANum a) w (AV (ANum v))). split; [exact H|].
rewrite Nat.eqb_refl, Z.eqb_refl. left. reflexivity.
Qed.

(* A cell's interval [a, e) lies in one of the pieces [ps] (a computation). *)
Definition in_pieces (ps : list (Z * Z)) (a e : Z) : bool := existsb (fun p => (fst p <=? a) && (e <=? snd p)) ps.
Lemma in_pieces_spec : forall ps a e, in_pieces ps a e = true -> exists p, In p ps /\ fst p <= a /\ e <= snd p.
Proof.
intros ps a e H. unfold in_pieces in H. apply existsb_exists in H as (p & Hp & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists p. auto.
Qed.

(* the layer's pw_ij (YGcfInstSec.v at 8aea1d52068), over YG0f.pairwise *)
Lemma pw_ij {X : Type} (R : X -> X -> Prop) : forall l i j x y, pairwise R l ->
  nth_error l i = Some x -> nth_error l (i + S j) = Some y -> R x y.
Proof.
induction l as [|h t IH]; intros i j x y P Hx Hy; [destruct i; discriminate|].
destruct P as [F P]. destruct i as [|i]; cbn in Hx, Hy.
- injection Hx as <-. apply (proj1 (Forall_forall _ _) F). exact (nth_error_In _ _ Hy).
- exact (IH i j x y P Hx Hy).
Qed.

Lemma le_byte_zero : forall w k, le_byte 0 w k = 0.
Proof. intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.

Lemma bv64_small : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Ha. Qed.

(* The view of a byte depends only on the memory at that byte (the layer's aview_same_g). *)
Lemma aview_same : forall segs (H : word -> bool) (mem mem' : word -> option byte) a,
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview segs H mem' a = aview segs H mem a.
Proof. intros segs H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

(* A cell holds at a reader that agrees on its bytes with a reader where it holds. *)
Lemma cell_holds_agree : forall B ly (rd rd' : reader) c,
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
  cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
intros B ly rd rd' c AG HC. unfold cell_holds in *. destruct (c_val c) as [e | mask v].
- intros k Hk. rewrite AG by lia. exact (HC k Hk).
- destruct HC as (b & Hb & Hm). exists b. split; [|exact Hm].
  pose proof (AG 0 ltac:(lia)) as E. rewrite Z.add_0_r in E. rewrite E. exact Hb.
Qed.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ================================================================================================================ *)
(* ZONE3 (YGcfInstSec.v:377-378 at 8aea1d52068): ims_zone3 is zone3 at AImgS_cgif, im_img_cover is img_cover.      *)
Lemma zone3_B : forall ly x sz, @im_img_cover AImg_cgif ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) ->
  ims_zone3 (AImgS := AImgS_cgif) x sz.
Proof. intros ly x sz C Hsz A D. exact (zone3_intro ly x sz C Hsz A D). Qed.

(* ================================================================================================================ *)
(* AREAS_DISJ (YGcfInstSec.v:752).                                                                                  *)
(* A layout to instantiate asyms_ok's const law with: Tfib_const does not read its layout. *)
Definition ly0 : alayout := ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0).

(* The four cells TfibSyms does not pin: each is the address of the only const cell of its width and value. *)
Lemma cells_B : forall B, @im_syms AImg_cgif B ->
  as_shadow_cell B = 0xab6f8 /\ as_uar_cell B = 0xab700 /\ as_got_shadow B = 0xa2850 /\ as_got_uar B = 0xa28a8.
Proof.
intros B TS. change (TfibSyms B) in TS.
destruct (aso_const_law B (ts_ok B TS) ly0) as (H1 & H2 & H3 & H4).
rewrite (ts_const B TS ly0) in H1, H2, H3, H4. unfold z8, z4, c8, c4 in H1, H2, H3, H4.
apply num_addrs_in in H1. apply num_addrs_in in H2.
assert (E1 : num_addrs 8 SHADOW_OFF (Tfib_const ly0) = [0xab6f8]) by (vm_compute; reflexivity).
assert (E2 : num_addrs 4 1 (Tfib_const ly0) = [0xab700]) by (vm_compute; reflexivity).
rewrite E1 in H1. rewrite E2 in H2.
destruct H1 as [S1|[]]. destruct H2 as [S2|[]]. rewrite <- S1 in H3. rewrite <- S2 in H4.
apply num_addrs_in in H3. apply num_addrs_in in H4.
assert (E3 : num_addrs 8 0xab6f8 (Tfib_const ly0) = [0xa2850]) by (vm_compute; reflexivity).
assert (E4 : num_addrs 8 0xab700 (Tfib_const ly0) = [0xa28a8]) by (vm_compute; reflexivity).
rewrite E3 in H3. rewrite E4 in H4.
destruct H3 as [S3|[]]. destruct H4 as [S4|[]].
split; [exact (eq_sym S1)|]. split; [exact (eq_sym S2)|]. split; [exact (eq_sym S3) | exact (eq_sym S4)].
Qed.

Lemma areas_disj_B : forall B, @im_syms AImg_cgif B -> pairwise zdisjoint (asyms_areas B).
Proof.
intros B TS. pose proof (cells_B B TS) as (E1 & E2 & E3 & E4). change (TfibSyms B) in TS.
unfold asyms_areas.
rewrite (ts_inst B TS), (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS),
  (ts_oom B TS), E1, E2, E3, E4, (ts_tp B TS).
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_OOM, TFIB_TP.
cbn [pairwise]. repeat match goal with
| |- _ /\ _ => split
| |- Forall _ (_ :: _) => constructor
| |- Forall _ [] => constructor
| |- True => exact I
| |- zdisjoint _ _ => unfold zdisjoint; cbn [fst snd]; lia
end.
Qed.

(* ================================================================================================================ *)
(* CONST_KEEP_S (YGcfInstSec.v:383-388).                                                                            *)

(* The mutex's pad bytes (inst + o_sec_mutex + 1 .. + 4) and AGif4.CZS's pieces at TFIB_INST that are numbers. *)
Definition padb (c : acell) : bool :=
  match c_at c, c_val c with
  | ANum a, AV (ANum 0) => (TFIB_INST + o_sec_mutex + 1 <=? a) && (a + Z.max 1 (Z.of_nat (c_w c)) <=? TFIB_INST + o_sec_mutex + 4)
  | _, _ => false
  end.
Definition czs_pieces : list (Z * Z) :=
  [(0x10000, TFIB_INST + o_sec_reserved); (TFIB_INST + o_sec_sorted + 1, TFIB_INST + o_sec_stats);
   (TFIB_INST + o_sec_stats + 32, TFIB_INST + 296); (TFIB_INST + 408, TFIB_INST + o_sec_mutex);
   (TFIB_INST + o_sec_mutex + 4, TFIB_INST + o_comb_stats); (TFIB_INST + o_comb_stats + 40, ims_img_end (AImgS := AImgS_cgif));
   (ims_shb (AImgS := AImgS_cgif), ims_csh_end (AImgS := AImgS_cgif)); (TFIB_TSD, TFIB_TSD + 8)].
Definition keep_okb (c : acell) : bool :=
  match c_at c with
  | ANum a => padb c || in_pieces czs_pieces a (a + Z.max 1 (Z.of_nat (c_w c)))
  | _ => false
  end.
Lemma keep_cells_ok : forallb keep_okb (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma czs_of_piece : forall ly p a, In p czs_pieces -> fst p <= a < snd p ->
  CZS (IM := AImg_cgif) (IMS := AImgS_cgif) ly TFIB_INST a.
Proof.
intros ly p a Hp Ha. unfold czs_pieces in Hp. cbn [In] in Hp. unfold CZS.
cbn [ims_img_end ims_shb ims_csh_end im_tsd AImgS_cgif AImg_cgif] in *.
repeat destruct Hp as [<-|Hp]; try destruct Hp; cbn [fst snd] in Ha;
  unfold AGjm.SHBv, TFIB_TSD in *; lia.
Qed.

(* Every byte of a const cell is in CZS, or the cell is a pad cell (its bytes 0, in the mutex's pad). *)
Lemma const_czs_B : forall B ly, TfibSyms B -> ly_tsd ly = as_tsd B -> forall c, In c (as_const B ly) ->
  (padb c = true) \/
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> CZS (IM := AImg_cgif) (IMS := AImgS_cgif) ly (as_inst B) (aeval B ly (c_at c) + k)).
Proof.
intros B ly TS TSD c Hin. rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. rewrite (ts_inst B TS).
pose proof (ts_tp B TS) as ETP. pose proof (ts_tsd B TS) as ETSD. pose proof (ts_inst B TS) as EIN.
apply in_app_iff in Hin as [Hin|Hin].
- right. unfold Tfib_const_sym in Hin. cbn [In] in Hin.
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [<-|Hin]; [intros k Hk; cbn [c_at c_w aeval z8 z4 z1 c8 c4 c1] in *; cbn in Hk;
      unfold CZS; cbn [ims_img_end ims_shb ims_csh_end im_tsd AImgS_cgif AImg_cgif];
      rewrite ?ETP, ?TSD, ?ETSD, ?EIN; unfold AGjm.SHBv, TFIB_TP, TFIB_TSD, TFIB_INST, o_space, o_rinfo, o_sec_chunks,
        o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *; lia |]
  | False => destruct Hin
  end.
- pose proof (proj1 (forallb_forall _ _) keep_cells_ok c Hin) as Hc. unfold keep_okb in Hc.
  destruct (c_at c) eqn:Ea; try discriminate.
  apply Bool.orb_prop in Hc as [Hp|Hp]; [left; exact Hp|].
  right. intros k Hk. apply in_pieces_spec in Hp as (p & Hp & H1 & H2).
  cbn [aeval]. apply (czs_of_piece ly p (z + k) Hp). lia.
Qed.

(* The bytes of CZS are words (the thread, ctx and D objects are application extents). *)
Lemma czs_range_B : forall ly a, layout_ok ly -> CZS (IM := AImg_cgif) (IMS := AImgS_cgif) ly TFIB_INST a -> 0 <= a < 2 ^ 64.
Proof.
intros ly a LY Ha. pose proof (lo_app ly LY) as HA. rewrite Forall_forall in HA.
pose proof (HA (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; right; right; left; reflexivity)) as IT.
pose proof (HA (ly_C ly, 256) ltac:(unfold owned_extents; do 6 right; left; reflexivity)) as IC.
pose proof (HA (ly_D ly, 4096) ltac:(unfold owned_extents; do 7 right; left; reflexivity)) as ID.
pose proof ASAN_CEIL_range as [CR _].
unfold in_app in IT, IC, ID. cbn [fst snd] in IT, IC, ID.
unfold CZS in Ha. cbn [ims_img_end ims_shb ims_csh_end im_tsd AImgS_cgif AImg_cgif] in Ha.
unfold AGjm.SHBv, TFIB_TSD, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats,
  kThreadObjSize, kLowShadowBeg, kHighMemBeg in *.
lia.
Qed.

Lemma const_keep_s_B : forall B, @im_syms AImg_cgif B ->
  forall ly (H : word -> bool) (mem0 mem : word -> option byte),
  layout_ok ly -> @im_img_cover AImg_cgif ly -> ly_tsd ly = as_tsd B ->
  Forall (cell_holds B ly (aview (@im_segs AImg_cgif) H mem0)) (as_const B ly) ->
  (forall x : word, ims_dzone (AImgS := AImgS_cgif) ly (bv_unsigned x) \/
     CZS (IM := AImg_cgif) (IMS := AImgS_cgif) ly (as_inst B) (bv_unsigned x) -> mem x = mem0 x) ->
  (forall k, 1 <= k < 4 -> aview (@im_segs AImg_cgif) H mem (as_inst B + o_sec_mutex + k) = Some 0) ->
  Forall (cell_holds B ly (aview (@im_segs AImg_cgif) H mem)) (as_const B ly).
Proof.
intros B TS ly H mem0 mem LY IMG TSD CST MEQ PAD. change (TfibSyms B) in TS.
apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) CST c Hc) as Hc0.
destruct (const_czs_B B ly TS TSD c Hc) as [P|Z].
- (* a pad cell: its value is 0 and its bytes are the mutex's pad bytes *)
  unfold padb in P. destruct (c_at c) eqn:Ea; try discriminate. destruct (c_val c) eqn:Ev; try discriminate.
  destruct e; try discriminate. destruct z0; try discriminate.
  apply andb_prop in P as [P1 P2]. apply Z.leb_le in P1. apply Z.leb_le in P2.
  unfold cell_holds. rewrite Ea, Ev. cbn [aeval]. intros k Hk. rewrite le_byte_zero.
  replace (z + Z.of_nat k) with (as_inst B + o_sec_mutex + (z + Z.of_nat k - (as_inst B + o_sec_mutex))) by lia.
  apply PAD. rewrite (ts_inst B TS). lia.
- (* a CZS cell: each byte keeps its view *)
  apply (cell_holds_agree B ly (aview (@im_segs AImg_cgif) H mem0)); [|exact Hc0].
  intros k Hk. pose proof (Z k Hk) as Hz. rewrite (ts_inst B TS) in Hz.
  pose proof (czs_range_B ly _ LY Hz) as R.
  apply aview_same. apply MEQ. right. rewrite (ts_inst B TS), (bv64_small _ R). exact Hz.
Qed.

(* ================================================================================================================ *)
(* CONST_NOT_JUNK (YGcfInstSec.v:748-750), snull_junk (:740-744) unfolded.                                          *)

(* The layer's msv_facts and bsl_bounds (YGcfInstSec.v at 8aea1d52068), over reply's ImgBaseAGS (the same text). *)
Lemma msv_facts : forall n, 64513 <= n < 2 ^ 30 ->
  73728 <= ImgBaseAGS.MSv n <= 262147 * 4096 /\ ImgBaseAGS.MSv n mod 4096 = 0 /\ n + 4096 <= ImgBaseAGS.MSv n.
Proof.
intros n Hn. unfold ImgBaseAGS.MSv, ImgBaseAGS.NDv, ImgBaseAGS.R8v.
pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as M1.
set (q := (n + 7) / 8) in *.
pose proof (Z.div_mod (q * 8 + 4096 + 4095) 4096 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (q * 8 + 4096 + 4095) 4096 ltac:(lia)) as M2.
set (p := (q * 8 + 4096 + 4095) / 4096) in *.
split; [lia|]. split; [|lia].
replace (p * 4096 + 4096) with ((p + 1) * 4096) by lia. apply Z_mod_mult.
Qed.
Lemma bsl_bounds : forall (regs0 : bvmap 5 word) n, 64513 <= n < 2 ^ 30 ->
  bv_unsigned (getr regs0 11) + 296 <= ImgBaseAGS.BSLv regs0 n /\ ImgBaseAGS.BSLv regs0 n + 8 <= bv_unsigned (getr regs0 11) + 416.
Proof.
intros regs0 n Hn. pose proof (msv_facts n Hn) as (M1 & _).
unfold ImgBaseAGS.BSLv, ImgBaseAGS.LGv.
assert (Q1 : 18 <= ImgBaseAGS.MSv n / 4096 <= 262147)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
pose proof (Z.log2_le_mono (ImgBaseAGS.MSv n / 4096) 262147 ltac:(lia)) as L2. rewrite (eq_refl : Z.log2 262147 = 18) in L2.
pose proof (Z.log2_le_mono 18 (ImgBaseAGS.MSv n / 4096) ltac:(lia)) as L1. rewrite (eq_refl : Z.log2 18 = 4) in L1.
lia.
Qed.
(* At reply's request bound (cf_malloc_max = 2 ^ 30 - 2 ^ 20) the map is below 2 ^ 30, so its log is at most 29 and the
   by_size_log word ends by inst + 408. *)
Lemma bsl_bounds_B : forall (regs0 : bvmap 5 word) n, 64513 <= n < 2 ^ 30 - 2 ^ 20 ->
  bv_unsigned (getr regs0 11) + 296 <= ImgBaseAGS.BSLv regs0 n /\ ImgBaseAGS.BSLv regs0 n + 8 <= bv_unsigned (getr regs0 11) + 408.
Proof.
intros regs0 n Hn. pose proof (bsl_bounds regs0 n ltac:(lia)) as [B1 _]. split; [exact B1|].
assert (M : ImgBaseAGS.MSv n <= n + 12294).
{ unfold ImgBaseAGS.MSv, ImgBaseAGS.NDv, ImgBaseAGS.R8v.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as M1.
  set (q := (n + 7) / 8) in *.
  pose proof (Z.div_mod (q * 8 + 4096 + 4095) 4096 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (q * 8 + 4096 + 4095) 4096 ltac:(lia)) as M2.
  set (p := (q * 8 + 4096 + 4095) / 4096) in *. lia. }
unfold ImgBaseAGS.BSLv, ImgBaseAGS.LGv.
assert (Q : ImgBaseAGS.MSv n / 4096 <= 262143) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.log2_le_mono _ 262143 Q) as L. rewrite (eq_refl : Z.log2 262143 = 17) in L. lia.
Qed.

(* The pieces the abs and shadow cells lie in: the image minus the instance's junk windows and the out-of-memory byte,
   and the shadow window. *)
Definition loc_pieces : list (Z * Z) :=
  [(0x10000, TFIB_INST + o_sec_sorted); (TFIB_INST + o_sec_sorted + 1, TFIB_INST + o_sec_stats);
   (TFIB_INST + o_sec_stats + 32, TFIB_INST + 296); (TFIB_INST + 408, TFIB_INST + o_comb_stats);
   (TFIB_INST + o_comb_stats + 40, TFIB_OOM); (TFIB_OOM + 1, TFIB_IMG_END);
   (ims_shb (AImgS := AImgS_cgif), ims_csh_end (AImgS := AImgS_cgif))].
Definition loc_okb (c : acell) : bool :=
  match c_at c with ANum a => in_pieces loc_pieces a (a + Z.max 1 (Z.of_nat (c_w c))) | _ => false end.
Lemma loc_cells_ok : forallb loc_okb (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

(* Where a const byte lies: an image byte outside the instance's junk windows and not the out-of-memory byte, a
   shadow byte, or a byte of the thread, ctx or D object. *)
Definition const_loc (ly : alayout) (a : Z) : Prop :=
  (TFIB_IMG_LO <= a < TFIB_IMG_END /\ ~ (TFIB_INST + o_sec_sorted <= a < TFIB_INST + o_sec_sorted + 1) /\
   ~ (TFIB_INST + o_sec_stats <= a < TFIB_INST + o_sec_stats + 32) /\ ~ (TFIB_INST + 296 <= a < TFIB_INST + 408) /\
   ~ (TFIB_INST + o_comb_stats <= a < TFIB_INST + o_comb_stats + 40) /\ a <> TFIB_OOM) \/
  (AGjm.SHBv <= a < 0x800b8200) \/ (ly_T ly <= a < ly_T ly + 80) \/ (ly_C ly <= a < ly_C ly + 160) \/
  (ly_D ly <= a < ly_D ly + 4096).

Lemma loc_of_piece : forall ly p a, In p loc_pieces -> fst p <= a < snd p -> const_loc ly a.
Proof.
intros ly p a Hp Ha. unfold loc_pieces in Hp. cbn [In] in Hp. unfold const_loc.
cbn [ims_shb ims_csh_end AImgS_cgif] in *.
repeat destruct Hp as [<-|Hp]; try destruct Hp; cbn [fst snd] in Ha;
  unfold AGjm.SHBv, TFIB_INST, TFIB_OOM, TFIB_IMG_LO, TFIB_IMG_END, o_sec_sorted, o_sec_stats, o_comb_stats in *; lia.
Qed.

Lemma const_loc_B : forall B ly, TfibSyms B -> ly_tsd ly = as_tsd B -> forall c, In c (as_const B ly) ->
  forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> const_loc ly (aeval B ly (c_at c) + k).
Proof.
intros B ly TS TSD c Hin k Hk. rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin.
pose proof (ts_tp B TS) as ETP. pose proof (ts_tsd B TS) as ETSD. pose proof (ts_inst B TS) as EIN.
apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin.
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [<-|Hin]; [cbn [c_at c_w aeval z8 z4 z1 c8 c4 c1] in *; cbn in Hk; unfold const_loc;
      rewrite ?ETP, ?TSD, ?ETSD, ?EIN; unfold AGjm.SHBv, TFIB_TP, TFIB_TSD, TFIB_INST, TFIB_OOM, TFIB_IMG_LO, TFIB_IMG_END,
        o_space, o_rinfo, o_sec_chunks, o_sec_sorted, o_sec_stats, o_comb_stats in *; lia |]
  | False => destruct Hin
  end.
- pose proof (proj1 (forallb_forall _ _) loc_cells_ok c Hin) as Hc. unfold loc_okb in Hc.
  destruct (c_at c) eqn:Ea; try discriminate. apply in_pieces_spec in Hc as (p & Hp & H1 & H2).
  cbn [aeval]. apply (loc_of_piece ly p (z + k) Hp). lia.
Qed.

Lemma const_not_junk_B : forall B, @im_syms AImg_cgif B ->
  forall ly (regs0 : bvmap 5 word) n c k, layout_ok ly -> @im_img_cover AImg_cgif ly -> ly_tsd ly = as_tsd B ->
  bv_unsigned (getr regs0 11) = as_inst B -> 64513 <= n < @cf_malloc_max CfParams_preset ->
  In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ ((ly_T ly + 2768 <= aeval B ly (c_at c) + k < ly_T ly + 2824) \/
     (ly_T ly + 2872 <= aeval B ly (c_at c) + k < ly_T ly + 2888) \/
     (ly_T ly + 2904 <= aeval B ly (c_at c) + k < ly_T ly + 2912) \/
     (as_inst B + o_sec_sorted <= aeval B ly (c_at c) + k < as_inst B + o_sec_sorted + 1) \/
     (as_inst B + o_sec_stats <= aeval B ly (c_at c) + k < as_inst B + o_sec_stats + 32) \/
     (ImgBaseAGS.BSLv regs0 n <= aeval B ly (c_at c) + k < ImgBaseAGS.BSLv regs0 n + 8) \/
     (as_inst B + o_comb_stats <= aeval B ly (c_at c) + k < as_inst B + o_comb_stats + 40) \/
     aeval B ly (c_at c) + k = as_oom_byte B).
Proof.
intros B TS ly regs0 n c k LY IMG TSD Hinst Hn Hc Hk. change (TfibSyms B) in TS.
pose proof (const_loc_B B ly TS TSD c Hc k Hk) as L.
remember (aeval B ly (c_at c) + k) as a eqn:Ea.
assert (Hn' : 64513 <= n < 2 ^ 30 - 2 ^ 20) by (cbn in Hn; lia).
pose proof (bsl_bounds_B regs0 n Hn') as BS. rewrite Hinst in BS.
rewrite (ts_inst B TS) in BS |- *. rewrite (ts_oom B TS).
(* the thread, ctx and D objects miss each other and the image; the thread object misses the shadow *)
pose proof (lo_disj ly LY) as DJ. unfold static_extents, owned_extents in DJ.
pose proof (pw_ij zdisjoint _ 2 3 _ _ DJ eq_refl eq_refl) as DTC.
pose proof (pw_ij zdisjoint _ 2 4 _ _ DJ eq_refl eq_refl) as DTD.
pose proof (pw_ij zdisjoint _ 2 6 _ _ DJ eq_refl eq_refl) as DTI.
pose proof (pw_ij zdisjoint _ 6 2 _ _ DJ eq_refl eq_refl) as DCI.
pose proof (pw_ij zdisjoint _ 7 1 _ _ DJ eq_refl eq_refl) as DDI.
unfold zdisjoint in DTC, DTD, DTI, DCI, DDI. cbn [fst snd] in DTC, DTD, DTI, DCI, DDI.
pose proof (lo_app ly LY) as HA. rewrite Forall_forall in HA.
pose proof (HA (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; right; right; left; reflexivity)) as IT.
unfold in_app in IT. cbn [fst snd] in IT.
destruct IMG as [IG1 IG2].
unfold const_loc in L.
clear - L BS DTC DTD DTI DCI DDI IT IG1 IG2.
unfold AGjm.SHBv, TFIB_INST, TFIB_OOM, TFIB_IMG_LO, TFIB_IMG_END, o_sec_sorted, o_sec_stats, o_comb_stats,
  kThreadObjSize, kLowShadowBeg, kHighMemBeg in *.
lia.
Qed.

End rows.
