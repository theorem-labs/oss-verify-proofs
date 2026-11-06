(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to libreac/fuzz_scene from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParseAcc.v at a working branch 603e40683a4 (the donor file carries no licence header -- it was lost on a Theorem Labs lane's side -- so the four lines above are this tree's, word for word the sibling segments' CtrlParseMid.v / CtrlParseNone.v lines): module paths and the listing layer renamed (Grant* -> Scene*, GS___ -> SS___, grant_listing -> scene_listing, KindOfLink1 -> P_kind_of_link1), TPARSE_STK taken from scene's reviewed P_reac_ctrl_parse.v. Every pc named in a comment is fuzz_scene.asan's (sha256 43654a025fd0...): reac_ctrl_parse = 0x83dd8, i.e. grant's pc + 0x1dd8; scene's reac_ctrl_parse has the same 616 instructions as grant's, so every instruction offset of the walk is the donor's. The atoms 32 (the shadow base) and 33 (the realigned sp) are entry atoms, not objects, so they keep their numbers; scene's shadow-base cell is object 16 and its side-stack flag object 17 (A_OBJ 16 / 17 = atoms 257 / 258), which this file touches only through pz_std's names. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/Prog/CtrlParseAcc.v, with its module paths, module names and numbers changed; 257 of its 628 lines of code are new or changed and 87 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated to libreac/fuzz_disco (from fuzz_grant's lib/A/Prog/CtrlParseAcc.v, a working branch 603e40683a4; the same code at other addresses): the walk takes fuzz_disco's context, whose contract names no caller frame for f and o, carries pz_kept in place of acall_kept, and takes the shadow facts of f and o from their places. *)
(* reac_ctrl_parse (0x873a8 of fuzz_disco's ASan image), the walk from cut M (0x874e8) to cut B (0x87570) on
   the path the header check accepts: the two memcpys of the addresses and the bcmp wrapper against .str.4
   ("\xff" x 6). The two shadow checks of the header bytes (0x87500, 0x87520) branch to the report stubs
   0x87af0 and 0x87afc, whose `jal __asan_report_load1` at 0x87af8 and 0x87b04 this walk refutes. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC81 YC4b YC1g YC1h YC45 YC85 DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParse CtrlParseLib KindOfLink1 DiscoRo ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import CtrlParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
(* The values of the walk's region bases in a hypothesis (pz_win_tac's rewriter). *)
Local Ltac acc_bases_in H :=
lazymatch goal with AGX : forall n, (n < 512)%nat -> ew _ n = ew _ n |- _ =>
rewrite ?(AGX 2%nat), ?(AGX 10%nat), ?(AGX 12%nat), ?(AGX 33%nat) in H by lia end;
lazymatch goal with Usp : bv_unsigned (ew ?E0 2) = _, B10 : bv_unsigned (ew ?E0 10) = _, B12 : bv_unsigned (ew ?E0 12) = _,
  B33 : bv_unsigned (ew ?E0 33) = _ |- _ => rewrite ?Usp, ?B10, ?B12, ?B33 in H end.
(* After a run: the valuation may hold fresh atoms (ewset) or a havoc above 512; carry AGX and the facts
   ew E n = v over to the new valuation, which gets a short name. *)
Local Ltac acc_ew_lo := cbn [extK]; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia].
Local Ltac acc_rebase HS AGX :=
let Ev := lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => Ev | st_ok _ ?Ev _ _ => Ev end in
lazymatch type of AGX with forall n, (n < ?L)%nat -> ew ?Eo n = ew ?E0 n =>
lazymatch Ev with
| Eo => idtac
| _ =>
  let En := fresh "E" in let HEv := fresh "HEv" in
  remember Ev as En eqn:HEv in *;
  let AGX2 := fresh "AGX" in
  assert (AGX2 : forall n, (n < L)%nat -> ew En n = ew E0 n)
    by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn; rewrite HEv; acc_ew_lo; apply AGX; exact Hnn);
  clear AGX; rename AGX2 into AGX;
  repeat match goal with H : ew Eo ?n = ?v |- _ =>
    let H2 := fresh in assert (H2 : ew En n = v) by (rewrite HEv; acc_ew_lo; exact H); clear H; rename H2 into H end;
  repeat match goal with H : img_env _ _ Eo |- _ => clear H end;
  clear HEv
end end.
(* lia over the walk's context: the disjunctive facts are boxed (lia would split on all of them at once); a goal
   that needs one of them gets it destructed, one at a time. *)
Local Ltac acc_lia :=
first [ lia
| match goal with H : boxed (_ \/ _) |- _ => let X := fresh in pose proof H as X; unfold boxed in X; destruct X; lia end
| match goal with H : boxed (_ /\ (_ \/ _)) |- _ => let X := fresh in pose proof H as X; unfold boxed in X; destruct X as [? [?|?]]; lia end
| match goal with H : boxed (off_img _ _) |- _ => let X := fresh in pose proof H as X; unfold boxed, off_img in X; destruct X; lia end
| match goal with H : boxed (in_app _ _) |- _ => let X := fresh in pose proof H as X; unfold boxed, in_app in X; destruct X as [? [?|?]]; lia end
| unbox; lia ].
(* The windows a run may write are inside Zs: carry pz_kept over the run (KOWN, pz_kept_own specialised to
   this walk), and give HKR, the run's memory outside Zs unchanged. *)
Local Ltac acc_hz Hs1 WSx := let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbv beta in Ha; unfold pz_nf; clear - Ha Hs1 WSx; lia.
Local Ltac acc_kept KOWN Zs HKR Hs1 WSx :=
lazymatch goal with HFr : frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) |- _ =>
lazymatch goal with HG : mem_grows (mrestrict _ mA) (mrestrict _ mB) |- _ =>
let Hw1 := fresh "Hw1" in
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi -> Zs a)
  by (pz_win_tac ltac:(fun H => acc_bases_in H; clear - H Hs1));
lazymatch goal with HAR : AR ?sg _ _ _ _ _ _ |- _ =>
pose proof (kept_of_frame (segs := sg) _ _ _ _ _ _ HFr Hw1) as HKR end;
lazymatch goal with KP : pz_kept _ _ _ _ _ _ _ _ _ |- _ =>
let KP' := fresh "KP" in
pose proof (KOWN mA mB Zs ltac:(acc_hz Hs1 WSx) KP HKR (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
clear KP Hw1; rename KP' into KP end end end.
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
(* The zero bytes of a region whose first chunk is CZero. *)
Lemma acc_zero_bytes : forall E (H : word -> bool) mem b n lo hi wlo whi rest,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some b) lo hi wlo whi (YP09.mkChunk 0 (CZero n) :: rest)) ->
forall i, 0 <= i < n -> aview SEGS H mem (bv_unsigned (ew E b) + i) = Some 0.
Proof.
intros E H mem b n lo hi wlo whi rest (_ & _ & _ & Hcs) i Hi.
apply Forall_inv in Hcs. destruct (Hcs i ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (bb & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb. injection Hb as <-.
cbn [base_val YP09.c_off YP09.r_base] in Hm. rewrite Z.add_0_r in Hm. unfold aview. cbv beta. rewrite Hm. reflexivity.
Qed.
(* The out struct at cut B (pz_out_cutB) from its 36 bytes. *)
Lemma acc_out_cutB : forall E (H : word -> bool) mem o fr,
bv_unsigned (ew E 12) = o -> 0 <= o -> o + 36 <= 2 ^ 64 ->
(forall i, 0 <= i < 36 -> apresent H mem (o + i)) ->
(forall i, (i < 6)%nat -> ew E (46 + i) = Z_to_bv 64 (cp_v fr (6 + i)) /\ ew E (40 + i) = Z_to_bv 64 (cp_v fr i)) ->
(forall i, 0 <= i < 4 \/ 16 <= i < 36 -> aview SEGS H mem (o + i) = Some 0) ->
(forall i, (i < 6)%nat -> aview SEGS H mem (o + 4 + Z.of_nat i) = Some (cp_v fr (6 + i))) ->
(forall i, (i < 6)%nat -> aview SEGS H mem (o + 10 + Z.of_nat i) = Some (cp_v fr i)) ->
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 12%nat) 0 36 0 36 pz_out_cutB).
Proof.
intros E H mem o fr H12 Ho0 Ho1 Hp HE Hz HB HA.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite H12.
split; [lia|]. split; [lia|]. split.
{ intros i Hi. apply (apresent_writable SEGS). apply Hp. lia. }
unfold pz_out_cutB. apply Forall_app. split.
{ constructor; [|constructor]. apply pz_chunk_zero. intros i Hi. rewrite Z.add_0_r. apply Hz. lia. }
apply Forall_app. split; [|apply Forall_app; split].
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
  apply (chunk_ok_val SEGS E _ o (4 + Z.of_nat i) 1 (SOff (46 + i) 0) (cp_v fr (6 + i))).
  + cbn [sv_denot]. rewrite (proj1 (HE i ltac:(lia))), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + pose proof (cp_v_range fr (6 + i)). change (8 * Z.of_N 1) with 8. lia.
  + change (Z.of_N 1) with 1. lia.
  + replace (o + (4 + Z.of_nat i)) with (o + 4 + Z.of_nat i) by lia. exact (proj1 (val_mem1_of_aview SEGS H mem _ _ (HB i ltac:(lia)))).
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
  apply (chunk_ok_val SEGS E _ o (10 + Z.of_nat i) 1 (SOff (40 + i) 0) (cp_v fr i)).
  + cbn [sv_denot]. rewrite (proj2 (HE i ltac:(lia))), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + pose proof (cp_v_range fr i). change (8 * Z.of_N 1) with 8. lia.
  + change (Z.of_N 1) with 1. lia.
  + replace (o + (10 + Z.of_nat i)) with (o + 10 + Z.of_nat i) by lia. exact (proj1 (val_mem1_of_aview SEGS H mem _ _ (HA i ltac:(lia)))).
- constructor; [|constructor]. apply pz_chunk_zero. intros i Hi. replace (o + 16 + i) with (o + (16 + i)) by lia. apply Hz. lia.
Qed.
(* The bcmp wrapper's answer against six 0xff bytes is cp_bcast (RcParse.v:32). *)
Lemma acc_bcast_iff : forall fr (P Q : Z -> option Z) f y,
(forall i, (i < 6)%nat -> P (f + Z.of_nat i) = Some (cp_v fr i)) ->
(forall i, 0 <= i < 6 -> Q (y + i) = Some 255) ->
((forall i, 0 <= i < 6 -> P (f + i) = Q (y + i)) <-> cp_bcast fr = true).
Proof.
intros fr P Q f y HP HQ. split.
- intros H.
  assert (Hk : forall k, (k < 6)%nat -> cp_v fr k = 255).
  { intros k Hk. pose proof (H (Z.of_nat k) ltac:(lia)) as X. rewrite (HP k Hk), (HQ (Z.of_nat k) ltac:(lia)) in X.
    injection X as X. exact X. }
  unfold cp_bcast. cbn [forallb].
  change (bv_unsigned (cp_b fr 0)) with (cp_v fr 0). change (bv_unsigned (cp_b fr 1)) with (cp_v fr 1).
  change (bv_unsigned (cp_b fr 2)) with (cp_v fr 2). change (bv_unsigned (cp_b fr 3)) with (cp_v fr 3).
  change (bv_unsigned (cp_b fr 4)) with (cp_v fr 4). change (bv_unsigned (cp_b fr 5)) with (cp_v fr 5).
  rewrite (Hk 0%nat), (Hk 1%nat), (Hk 2%nat), (Hk 3%nat), (Hk 4%nat), (Hk 5%nat) by lia. reflexivity.
- intros H i Hi. unfold cp_bcast in H. cbn [forallb] in H. rewrite !andb_true_iff in H.
  destruct H as (H0 & H1 & H2 & H3 & H4 & H5 & _). apply Z.eqb_eq in H0, H1, H2, H3, H4, H5.
  rewrite (HQ i Hi). pose proof (HP (Z.to_nat i) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia. rewrite X. f_equal.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; assumption.
Qed.
(* A range none of whose bytes is the own frame lies below or above it. *)
Lemma acc_sep : forall F FL p n, 0 < n -> (forall a, p <= a < p + n -> ~ pz_nf F FL a) -> p + n <= F \/ F + 128 <= p.
Proof.
intros F FL p n Hn H. destruct (Z_le_gt_dec (p + n) F) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (F + 128) p) as [H2|H2]; [right; exact H2|].
exfalso. apply (H (Z.max p F)); [lia|]. left. lia.
Qed.
(* The shadow hull of a range is the union of the hulls of its bytes. *)
Lemma acc_hull_bytes : forall (rd : reader) p n, 0 <= p -> 0 < n ->
(forall x, p <= x < p + n -> shadow_hull_vis rd x 1) -> shadow_hull_vis rd p n.
Proof.
intros rd p n Hp Hn H s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
set (x := Z.max p (64 * (s / 8) - 8 * 2147450880)).
assert (Hx : p <= x < p + n) by (unfold x; lia).
apply (H x Hx s). unfold x, shadow_addr, SHADOW_OFF. lia.
Qed.
(* The shadow entries of the two objects, from their shadow bytes at the current memory (the frame f may
   lie on the machine stack, above the allocation ceiling). *)
Lemma acc_shok : forall E H mem f o,
ew E 10 = Z_to_bv 64 f -> ew E 12 = Z_to_bv 64 o -> ew E 32 = Z_to_bv 64 SB ->
0 < f -> f + 50 <= 2 ^ 47 -> (f + 50 <= kLowShadowBeg \/ kHighMemBeg <= f) ->
0 < o -> o + 36 <= 2 ^ 47 -> (o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) ->
range_addressable (aview SEGS H mem) SHADOW_OFF f 50 -> range_addressable (aview SEGS H mem) SHADOW_OFF o 36 ->
sh_ok SEGS PZx PZ_SH E (mrestrict H mem).
Proof.
intros E H mem f o E10 E12 E32 Hf0 Hf47 Hfsh Ho0 Ho47 Hosh HRf HRo.
unfold sh_ok, PZ_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS H mem E PZx 10 f 50 f 0 50 HRf).
+ unfold U, PZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia.
+ intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- apply (shent_ok_of_range SEGS H mem E PZx 12 o 36 o 0 36 HRo).
+ unfold U, PZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia.
+ intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Section m.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* The shadow byte of a byte of a caller frame is no byte of the out struct (an application range). *)
Lemma acc_frame_sh : forall lyc Sc W memc mdc cid pos o x,
AR SEGS B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) -> ~ (o <= shadow_addr x < o + 36).
Proof.
intros lyc Sc W memc mdc cid pos o x HAR Hin Hx Hoap.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (G4 & Gce & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE. unfold ASAN_CEIL in HCE.
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* Where each byte of the out struct lies: a caller block or a caller frame (the machine stack is above
   the allocation ceiling, and the shadow of a caller frame holds no application byte). *)
Lemma acc_out_loc : forall STK sp0 FP ly S lyc Sc own W memc mdc o x,
AR SEGS B lyc Sc W memc mdc ->
(forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)) ->
alloc_ceiling <= sp0 - STK -> o + 36 <= alloc_ceiling ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) -> o <= x < o + 36 ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x ->
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= x < b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid).
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc o x HAR Hown Hstk Hoce Hoap Hx Hw.
destruct Hw as [Hs|[(_ & b & m & Hb & Hr)|[(b & m & Hb & _ & Hr)|(cid & pos & Hin & [Hr|Hr])]]].
- lia.
- left. exists b, m. split; [exact Hb | lia].
- left. exists b, m. split; [exact Hb | lia].
- right. exists cid, pos. split; [exact (Hown cid pos Hin)|]. unfold in_zr in Hr. cbn [fst snd] in Hr. lia.
- exfalso. destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR (Hown cid pos Hin)) as (G4 & Gce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE. unfold ASAN_CEIL in HCE.
unfold in_zr in Hr. cbn [fst snd] in Hr.
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* A part [p, p + n) of the out struct stays addressable and its shadow hull readable: a byte in a caller
   block has them from the state, a byte in a caller frame keeps its shadow byte (pz_kept) and has its hull
   from the state. *)
Lemma acc_out_shadow : forall STK sp0 FP ly S lyc Sc own W memc mdc S2 mem2 md2 slo shi o p n,
AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc S2 W mem2 md2 ->
(forall cid pos, In (cid, pos) own -> In (cid, pos) (frames Sc)) ->
(forall c' p', In (c', p') (frames Sc) -> In (c', p') (frames S2)) -> ablocks B lyc S2 = ablocks B lyc Sc ->
alloc_ceiling <= sp0 - STK -> o + 36 <= alloc_ceiling -> 4096 <= o ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) ->
pz_kept B lyc Sc W memc mem2 slo shi o ->
(forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o 36 ->
o <= p -> p + n <= o + 36 -> 0 < n ->
range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF p n /\ shadow_hull_vis (aview SEGS (w_H W) mem2) p n.
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc S2 mem2 md2 slo shi o p n HAR HAR2 Hown HfinS2 Eab Hstk Hoce Ho4 Hoap KP HOW HRo
Hp Hpn Hn.
assert (L : forall x, p <= x < p + n ->
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= x < b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid))
by (intros x Hx; exact (acc_out_loc STK sp0 FP ly S lyc Sc own W memc mdc o x HAR Hown Hstk Hoce Hoap ltac:(lia) (HOW x ltac:(lia)))).
split.
- intros x Hx. destruct (L x Hx) as [(b & m & Hb & Hr)|(cid & pos & Hin & Hr)].
+ rewrite <- Eab in Hb. exact (range_addressable_of_block SEGS B LAWS lyc S2 W mem2 md2 b m x 1 HAR2 Hb ltac:(lia) ltac:(lia) x ltac:(lia)).
+ refine (pz_kept_ra B LAWS lyc Sc W memc mdc mem2 slo shi o cid pos x 1 HAR KP Hin ltac:(lia) ltac:(lia) _ _ x ltac:(lia)).
* intros y Hy. exact (acc_frame_sh lyc Sc W memc mdc cid pos o y HAR Hin ltac:(lia) Hoap).
* intros y Hy. apply HRo. lia.
- apply acc_hull_bytes; [lia | lia |]. intros x Hx. destruct (L x Hx) as [(b & m & Hb & Hr)|(cid & pos & Hin & Hr)].
+ rewrite <- Eab in Hb. exact (shadow_hull_vis_of_block SEGS B LAWS lyc S2 W mem2 md2 b m x 1 HAR2 Hb ltac:(lia) ltac:(lia) ltac:(lia)).
+ exact (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W mem2 md2 cid pos x 1 HAR2 (HfinS2 _ _ Hin) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
(* The bytes of the frame f are kept: it lies in a caller frame, a caller block or on the machine stack
   (above the allocation ceiling), outside the call's stack window and apart from the out struct. *)
Lemma acc_f_kept : forall lyc Sc W memc memX slo shi o f a,
pz_kept B lyc Sc W memc memX slo shi o -> pz_loc B lyc Sc f 50 ->
alloc_ceiling <= ly_stk_lo lyc -> f + 50 <= 2 ^ 47 ->
(shi <= f \/ f + 50 <= slo) -> (o + 36 <= f \/ f + 50 <= o) ->
f <= a < f + 50 -> aview SEGS (w_H W) memX a = aview SEGS (w_H W) memc a.
Proof.
intros lyc Sc W memc memX slo shi o f a (K1 & K2 & _ & K4 & _) Hloc Hstk Hf47 Hwin Hdfo Ha.
destruct Hloc as [(cid & pos & Hin & Hlo & Hhi)|[(b & m & Hb & Hlo & Hhi)|(Hlo & Hhi)]].
- apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | lia].
- replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hb); lia.
- apply K1; lia.
Qed.
(* The frame f stays addressable: in a caller frame it keeps its shadow bytes (pz_kept), in a caller block
   or on the machine stack (zero shadow) it has them from the state. *)
Lemma acc_f_ra : forall lyc Sc W memc mdc S2 mem2 md2 slo shi o f,
AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc S2 W mem2 md2 -> ablocks B lyc S2 = ablocks B lyc Sc ->
pz_kept B lyc Sc W memc mem2 slo shi o -> pz_loc B lyc Sc f 50 ->
(o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF f 50 ->
range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF f 50.
Proof.
intros lyc Sc W memc mdc S2 mem2 md2 slo shi o f HAR HAR2 Eab KP Hloc Hoap HRf.
destruct Hloc as [(cid & pos & Hin & Hlo & Hhi)|[(b & m & Hb & Hlo & Hhi)|(Hlo & Hhi)]].
- apply (pz_kept_ra B LAWS lyc Sc W memc mdc mem2 slo shi o cid pos f 50 HAR KP Hin Hlo Hhi); [|exact HRf].
intros y Hy. exact (acc_frame_sh lyc Sc W memc mdc cid pos o y HAR Hin ltac:(lia) Hoap).
- rewrite <- Eab in Hb. exact (range_addressable_of_block SEGS B LAWS lyc S2 W mem2 md2 b m f 50 HAR2 Hb Hlo Hhi).
- pose proof (al_zshadow _ _ LAWS lyc S2 W mem2 md2 (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR2 (or_introl eq_refl)) as Hz.
cbn [fst snd] in Hz.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR2))) as (_ & _ & _ & _ & T5 & T6 & _). unfold page_aligned in T5, T6.
apply (range_addressable_sub _ SHADOW_OFF (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc) f 50); [| lia | lia].
apply zero_shadow_range; [lia | lia | exact Hz].
Qed.
(* The shadow hull of a part [p, p + n) of the frame f is readable at a state with the call's frame: a
   caller frame or block has it from the state, the machine stack has zero shadow. *)
Lemma acc_f_hull : forall lyc Sc S2 W mem2 md2 f p n,
AR SEGS B lyc S2 W mem2 md2 -> ablocks B lyc S2 = ablocks B lyc Sc ->
(forall c' p', In (c', p') (frames Sc) -> In (c', p') (frames S2)) ->
pz_loc B lyc Sc f 50 -> f <= p -> p + n <= f + 50 -> 0 < n ->
shadow_hull_vis (aview SEGS (w_H W) mem2) p n.
Proof.
intros lyc Sc S2 W mem2 md2 f p n HAR2 Eab HfinS2 Hloc Hp Hpn Hn.
destruct Hloc as [(cid & pos & Hin & Hlo & Hhi)|[(b & m & Hb & Hlo & Hhi)|(Hlo & Hhi)]].
- exact (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W mem2 md2 cid pos p n HAR2 (HfinS2 _ _ Hin) ltac:(lia) ltac:(lia) Hn).
- rewrite <- Eab in Hb. exact (shadow_hull_vis_of_block SEGS B LAWS lyc S2 W mem2 md2 b m p n HAR2 Hb ltac:(lia) ltac:(lia) Hn).
- pose proof (al_zshadow _ _ LAWS lyc S2 W mem2 md2 (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR2 (or_introl eq_refl)) as Hz.
cbn [fst snd] in Hz.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR2))) as (_ & _ & _ & _ & T5 & T6 & _). unfold page_aligned in T5, T6.
intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
assert (Hi : 0 <= s - (SHADOW_OFF + ly_stk_lo lyc / 8) < (ly_stk_hi lyc - ly_stk_lo lyc) / 8) by (unfold SHADOW_OFF; lia).
pose proof (Hz _ Hi) as Hzs. unfold shadow_of_addr in Hzs.
replace (SHADOW_OFF + ly_stk_lo lyc / 8 + (s - (SHADOW_OFF + ly_stk_lo lyc / 8))) with s in Hzs by lia.
rewrite Hzs. discriminate.
Qed.
End m.
Lemma pz_segAcc : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutB_spec B c ->
pz_cutM_case B c (cp_hdr (cx_n c) (cx_fr c) = true).
Proof.
intros B G RT c Hok HcB Hbig E ms md Hcur HS SHOK Hhdr.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_open_f Hbig. pz_std.
pose proof (proj1 (cp_hdr_spec n fr) Hhdr) as (Hn50 & Hf12 & Hf13).
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
(* Facts about the two caller objects f and o, used at every step. *)
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCE. unfold ASAN_CEIL in HCE.
pose proof HJ as (_ & Hlyc & _). pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
assert (Hstk : alloc_ceiling <= sp0 - STK) by (clear - Hceil Hslo; lia).
assert (Hslo2 : alloc_ceiling <= sp - REAC_CTRL_PARSE_STK) by (clear - Hstk Hwin; lia).
assert (Hshi2 : sp <= 2 ^ 64) by (clear - Hsp0 Hshi H47; lia).
assert (Hstklo : alloc_ceiling <= ly_stk_lo lyc) by (rewrite Eslo; clear - Hceil; lia).
assert (HsepO : o + 36 <= F \/ F + 128 <= o).
{ apply (acc_sep F FL o 36 ltac:(lia)). intros a Ha.
  exact (pz_awr_nf B STK sp0 FP ly S lyc Sc own W memc mdc a F FL HAR Hownf N1 N3 N4 Hstk (proj1 (HOW a Ha))). }
pose proof Hosh as Hosh'. unfold kLowShadowBeg, kHighMemBeg in Hosh'.
repeat match goal with H : _ \/ _ |- _ => box H | H : off_img _ _ |- _ => box H | H : in_app _ _ |- _ => box H end.
(* The frame f's bytes at the entry, and at every memory pz_kept relates to it. *)
assert (FR0 : forall i, (i < 50)%nat -> aview SEGS (w_H W) memc (f + Z.of_nat i) = Some (cp_v fr i)).
{ intros i Hi. assert (Hl : (i < length (map (fun b : byte => bv_unsigned b) fr))%nat) by (rewrite length_map, Hflen; lia).
  pose proof (proj1 (HGf i Hl)) as Hv.
  replace (nth i (map (fun b : byte => bv_unsigned b) fr) 0) with (cp_v fr i) in Hv.
  - exact (aview_of_val_mem1 SEGS (w_H W) memc _ _ Hv (cp_v_range fr i)).
  - unfold cp_v, cp_b. rewrite (nth_indep _ 0 (bv_unsigned cp_z)) by (rewrite length_map, Hflen; lia).
    symmetry. apply (map_nth (fun b : byte => bv_unsigned b) fr cp_z i). }
(* The out struct is present at every memory of the journal: each of its bytes is one the caller may write. *)
assert (HOp : forall m md', ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 W m md' k ->
  forall a, o <= a < o + 36 -> apresent (w_H W) m a).
{ intros m md' HJx a Ha.
  assert (Hw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((1, fpos) :: own) a)
  by (rewrite Eab; apply pz_awr_cons; exact (proj1 (HOW a Ha))).
  exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJx Hw)). }
assert (KOWN : forall memX memY (Zs : Z -> Prop),
  (forall a, Zs a -> (sp - REAC_CTRL_PARSE_STK <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) ->
  pz_kept B lyc Sc W memc memX (sp - REAC_CTRL_PARSE_STK) sp o ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) memY a = aview SEGS (w_H W) memX a) ->
  (forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
  pz_kept B lyc Sc W memc memY (sp - REAC_CTRL_PARSE_STK) sp o).
{ intros memX memY Zs HZ KPX Hkp Hgr.
  exact (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ memX memY (sp - REAC_CTRL_PARSE_STK) sp o fpos F FL Zs
    HAR HARc Hfrs2 Eab EF EFL FFL Hslo2 Hshi2 Hoimg HZ KPX Hkp Hgr). }
assert (FB : forall memX, pz_kept B lyc Sc W memc memX (sp - REAC_CTRL_PARSE_STK) sp o ->
  forall i, (i < 50)%nat -> aview SEGS (w_H W) memX (f + Z.of_nat i) = Some (cp_v fr i)).
{ intros memX KPX i Hi.
  rewrite (acc_f_kept B lyc Sc W memc memX _ _ o f (f + Z.of_nat i) KPX Hfloc Hstklo Hf47 Hfwin Hdfo ltac:(lia)).
  exact (FR0 i Hi). }
assert (FBN : forall memX, pz_kept B lyc Sc W memc memX (sp - REAC_CTRL_PARSE_STK) sp o ->
  forall a, f <= a < f + 50 -> aview SEGS (w_H W) memX a <> None).
{ intros memX KPX a Ha. replace a with (f + Z.of_nat (Z.to_nat (a - f))) by lia. rewrite (FB memX KPX) by lia. discriminate. }
assert (RAF : forall memX mdX, AR SEGS B lyc S2 W memX mdX -> pz_kept B lyc Sc W memc memX (sp - REAC_CTRL_PARSE_STK) sp o ->
  range_addressable (aview SEGS (w_H W) memX) SHADOW_OFF f 50)
  by (intros memX mdX HA KPX; exact (acc_f_ra B LAWS lyc Sc W memc mdc S2 memX mdX _ _ o f HAR HA Eab KPX Hfloc Hosh HRf)).
assert (HUF : forall memX mdX p0 k0, AR SEGS B lyc S2 W memX mdX -> f <= p0 -> p0 + k0 <= f + 50 -> 0 < k0 ->
  shadow_hull_vis (aview SEGS (w_H W) memX) p0 k0)
  by (intros memX mdX p0 k0 HA Hp Hpk Hk; exact (acc_f_hull B LAWS lyc Sc S2 W memX mdX f p0 k0 HA Eab HfinS2 Hfloc Hp Hpk Hk)).
assert (OSH : forall memX mdX p0 k0, AR SEGS B lyc S2 W memX mdX ->
  pz_kept B lyc Sc W memc memX (sp - REAC_CTRL_PARSE_STK) sp o -> o <= p0 -> p0 + k0 <= o + 36 -> 0 < k0 ->
  range_addressable (aview SEGS (w_H W) memX) SHADOW_OFF p0 k0 /\ shadow_hull_vis (aview SEGS (w_H W) memX) p0 k0)
  by (intros memX mdX p0 k0 HA KPX Hp Hpk Hk;
      exact (acc_out_shadow B LAWS STK sp0 FP ly S lyc Sc own W memc mdc S2 memX mdX _ _ o p0 k0
        HAR HA Hownf HfinS2 Eab Hstk Howin Ho4096 Hosh KPX (fun a Ha => proj1 (HOW a Ha)) HRo Hp Hpk Hk)).
assert (SHOKF : forall Ex memX mdX, ew Ex 10 = Z_to_bv 64 f -> ew Ex 12 = Z_to_bv 64 o -> ew Ex 32 = Z_to_bv 64 SB ->
  AR SEGS B lyc S2 W memX mdX -> pz_kept B lyc Sc W memc memX (sp - REAC_CTRL_PARSE_STK) sp o ->
  sh_ok SEGS PZx PZ_SH Ex (mrestrict (w_H W) memX)).
{ intros Ex memX mdX X10 X12 X32 HA KPX.
  apply (acc_shok Ex (w_H W) memX f o X10 X12 X32); [lia | exact Hf47 | exact Hfsh | lia | exact Ho47 | exact Hosh
  | exact (RAF _ _ HA KPX) | exact (proj1 (OSH _ _ o 36 HA KPX ltac:(lia) ltac:(lia) ltac:(lia)))]. }
(* 1. The header checks: n >= 50 (0x874ec), f[12] = 0x88 (0x8750c), f[13] = 0x19 (0x8752c); the shadow checks of
   f + 12 and f + 13 (0x87500, 0x87520, to the report stubs at 0x87af0 / 0x87afc) are taken by the run from sh_ok. *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
acc_kept KOWN (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HKR Hsp1r WS. clear HKR HF HFr HG. acc_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan.
{ exfalso. clear HS. rewrite branch_ltu_U, U_SLit in Hc.
  rewrite (U_atom _ 11%nat n) in Hc by (first [rewrite (AGX 11%nat) by lia; exact E11 | lia]).
  rewrite (zcanon_id 50) in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
acc_kept KOWN (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HKR Hsp1r WS. clear HKR HF HFr HG. acc_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan.
{ exfalso. clear HS. rewrite branch_ne_U, U_SLit in Hc.
  rewrite (U_atom _ 52%nat (cp_v fr 12)) in Hc by (first [rewrite (AGX 52%nat) by lia; exact (EFB 12%nat ltac:(lia)) | pose proof (cp_v_range fr 12); lia]).
  rewrite Hf12 in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
acc_kept KOWN (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HKR Hsp1r WS. clear HKR HF HFr HG. acc_rebase HS AGX.
psrr_branch_tok RUN BR HS SHOK PZspan.
{ exfalso. clear HS. rewrite branch_ne_U, U_SLit in Hc.
  rewrite (U_atom _ 53%nat (cp_v fr 13)) in Hc by (first [rewrite (AGX 53%nat) by lia; exact (EFB 13%nat ltac:(lia)) | pose proof (cp_v_range fr 13); lia]).
  rewrite Hf13 in Hc. vm_compute in Hc. discriminate Hc. }
(* 2. checked_memcpy(o + 10, f, 6) at 0x87548 (s4 = o is not 0, so s6 = o: the branch at 0x87534 is decided by
   o's fact). The out struct is dropped from the state; its bytes are carried as facts (OZ1, OA). *)
clear Hc.
paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
acc_kept KOWN (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36)) HKR Hsp1r WS. clear HKR HF HFr HG. acc_rebase HS AGX.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (OZ : forall j, 0 <= j < 36 -> aview SEGS (w_H W) (ms_mem msX) (o + j) = Some 0) end.
{ intros j Hj. pose proof (YC4b.st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as R12.
  cbn [ms_mem restrict] in R12. pose proof (acc_zero_bytes _ _ _ _ _ _ _ _ _ _ R12 j Hj) as Z0.
  rewrite (AGX 12%nat), B12 in Z0 by lia. exact Z0. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (HspT : spZ (ms_regs msX) = sp1) by (unfold spZ; rewrite Rsp, (AGX 33%nat), B33 by lia; reflexivity) end.
pmkst HS.
eapply SRr_bind.
{ clear HS. lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA DS___asan_memcpy) (AMEMCPY fq) W rT mT
    STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 dT k (o + 10) f 6 (sp1 - sp0) _ HJ2) end.
  - rewrite Ra0, (AGX 12%nat), B12 by lia. reflexivity.
  - rewrite Ra1, (AGX 10%nat), E10 by lia. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite HspT. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite Rgp, (AGX 3%nat), (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite Rtp, (AGX 4%nat), (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [rewrite Eab; apply pz_awr_cons; exact (proj1 (HOW a ltac:(lia))) | rewrite Hes; lia].
  - clear - Hoam. unfold amem_range in *. lia.
  - exact (proj1 (OSH _ _ (o + 10) 6 (proj1 HJ2) KP ltac:(lia) ltac:(lia) ltac:(lia))).
  - intros _. exact (proj2 (OSH _ _ (o + 10) 6 (proj1 HJ2) KP ltac:(lia) ltac:(lia) ltac:(lia))).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [apply (FBN _ KP); lia | rewrite HspT, Hes; acc_lia]. }
    split; [acc_lia|]. split.
    { clear - Hfam. unfold amem_range in *. lia. }
    split; [intros x Hx; apply (RAF _ _ (proj1 HJ2) KP); lia|].
    intros _. apply (HUF _ _ f 6 (proj1 HJ2)); lia. }
cbv beta. intros W2 c2 _ (-> & rA & memA & mdA & -> & HJX & HP2 & Ha0' & Heff & Hfrc & Hpres2). cbv iota in Heff.
(* After the copy: o + 10 .. o + 15 hold f[0..5], the rest of the out struct is still zero. *)
lazymatch type of Hfrc with forall a, _ -> _ -> _ -> aview _ _ _ a = aview _ _ ?mT a =>
assert (OA : forall j, (j < 6)%nat -> aview SEGS (w_H W) memA (o + 10 + Z.of_nat j) = Some (cp_v fr j))
  by (clear HS; intros j Hj; rewrite (Heff (Z.of_nat j)) by lia; apply (FB mT KP); lia);
assert (OZ1 : forall j, 0 <= j < 10 \/ 16 <= j < 36 -> aview SEGS (w_H W) memA (o + j) = Some 0)
  by (clear HS; intros j Hj; rewrite Hfrc by (rewrite ?Hes; lia); apply OZ; lia);
assert (HKC : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp1 - 4096 <= a < sp1) \/ (o + 10 <= a < o + 16)) ->
  aview SEGS (w_H W) memA a = aview SEGS (w_H W) mT a)
  by (intros a Ha Hna; apply Hfrc; [exact Ha | clear - Hna; lia | rewrite Hes; clear - Hna; lia]);
let KP' := fresh "KP" in
pose proof (KOWN mT memA (fun a => (sp1 - 4096 <= a < sp1) \/ (o + 10 <= a < o + 16)) ltac:(acc_hz Hsp1r WS) KP HKC Hpres2) as KP';
clear KP; rename KP' into KP end.
clear OZ HKC Heff.
jafter_call_keep_hi HS 760%nat rA (mrestrict (w_H W) memA) HP2 [1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
{ clear HS HS2. cbn [ms_mem restrict]. pose proof KP as (_ & _ & _ & _ & _ & KP6). repeat apply Forall_cons; try apply Forall_nil.
  - apply (pz_region_kept _ _ _ _ 529%nat (SB + F / 8)); [rewrite E529; apply unsigned_lit_small; unfold SB; lia | intros a Ha; unfold SB in Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; lia].
  - apply (pz_region_kept _ _ _ _ 516%nat F); [rewrite RF; apply unsigned_lit_small; lia | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; lia].
  - apply (pz_region_kept _ _ _ _ 33%nat sp1); [rewrite (AGX 33%nat) by lia; exact B33 | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; apply KP6; lia].
  - apply (pz_region_kept _ _ _ _ 2%nat sp); [rewrite (AGX 2%nat) by lia; exact Usp | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; apply KP6; lia].
  - apply (pz_region_kept _ _ _ _ 10%nat f); [rewrite (AGX 10%nat) by lia; exact B10 | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS Hfrc HP2 Hpres2 Ha0'; rename HS2 into HS.
pz_rebase HS AGX.
clear SHOK. pose proof (SHOKF _ memA _ ltac:(rewrite (AGX 10%nat) by lia; exact E10) ltac:(rewrite (AGX 12%nat) by lia; exact E12)
  ltac:(rewrite (AGX 32%nat) by lia; exact E32) (proj1 HJX) KP) as SHOK.
clear HJ2. rename HJX into HJ2.
(* 3. checked_memcpy(o + 4, f + 6, 6) at 0x87558. *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
acc_kept KOWN (fun a => sp1 <= a < sp) HKR Hsp1r WS.
lazymatch type of HKR with forall a, _ -> _ -> aview _ _ ?mB a = aview _ _ ?mA a =>
assert (OZ1' : forall j, 0 <= j < 10 \/ 16 <= j < 36 -> aview SEGS (w_H W) mB (o + j) = Some 0)
  by (clear HS; intros j Hj; rewrite HKR; [apply OZ1; exact Hj | lia | cbv beta; lia]);
assert (OA' : forall j, (j < 6)%nat -> aview SEGS (w_H W) mB (o + 10 + Z.of_nat j) = Some (cp_v fr j))
  by (clear HS; intros j Hj; rewrite HKR; [apply OA; exact Hj | lia | cbv beta; lia]) end.
clear OZ1 OA HKR HF HFr HG. rename OZ1' into OZ1. rename OA' into OA. acc_rebase HS AGX.
prreg HS (10%bv : bv 5) Rb0. prreg HS (11%bv : bv 5) Rb1. prreg HS (12%bv : bv 5) Rb2.
prreg HS (1%bv : bv 5) Rbra. prreg HS (2%bv : bv 5) Rbsp. prreg HS (3%bv : bv 5) Rbgp. prreg HS (4%bv : bv 5) Rbtp.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (HspT2 : spZ (ms_regs msX) = sp1) by (unfold spZ; rewrite Rbsp, (AGX 33%nat), B33 by lia; reflexivity) end.
pmkst HS.
eapply SRr_bind.
{ clear HS. lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA DS___asan_memcpy) (AMEMCPY fq) W rT mT
    STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 dT k (o + 4) (f + 6) 6 (sp1 - sp0) _ HJ2) end.
  - rewrite Rb0, (AGX 12%nat), B12 by lia. reflexivity.
  - rewrite Rb1, (AGX 10%nat), B10 by lia. reflexivity.
  - rewrite Rb2. reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite HspT2. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite Rbgp, (AGX 3%nat), (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite Rbtp, (AGX 4%nat), (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - exact Rbra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [rewrite Eab; apply pz_awr_cons; exact (proj1 (HOW a ltac:(lia))) | rewrite Hes; lia].
  - clear - Hoam. unfold amem_range in *. lia.
  - exact (proj1 (OSH _ _ (o + 4) 6 (proj1 HJ2) KP ltac:(lia) ltac:(lia) ltac:(lia))).
  - intros _. exact (proj2 (OSH _ _ (o + 4) 6 (proj1 HJ2) KP ltac:(lia) ltac:(lia) ltac:(lia))).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [apply (FBN _ KP); lia | rewrite HspT2, Hes; acc_lia]. }
    split; [acc_lia|]. split.
    { clear - Hfam. unfold amem_range in *. lia. }
    split; [intros x Hx; apply (RAF _ _ (proj1 HJ2) KP); lia|].
    intros _. apply (HUF _ _ (f + 6) 6 (proj1 HJ2)); lia. }
cbv beta. intros W2 c2 _ (-> & rB & memB & mdB & -> & HJX & HP2 & Hb0' & Heff & Hfrc & Hpres2). cbv iota in Heff.
lazymatch type of Hfrc with forall a, _ -> _ -> _ -> aview _ _ _ a = aview _ _ ?mT a =>
assert (OB : forall j, (j < 6)%nat -> aview SEGS (w_H W) memB (o + 4 + Z.of_nat j) = Some (cp_v fr (6 + j)))
  by (clear HS; intros j Hj; rewrite (Heff (Z.of_nat j)) by lia; replace (f + 6 + Z.of_nat j) with (f + Z.of_nat (6 + j)) by lia;
      apply (FB mT KP); lia);
assert (OZ2 : forall j, 0 <= j < 4 \/ 16 <= j < 36 -> aview SEGS (w_H W) memB (o + j) = Some 0)
  by (clear HS; intros j Hj; rewrite Hfrc by (rewrite ?Hes; lia); apply OZ1; lia);
assert (OA' : forall j, (j < 6)%nat -> aview SEGS (w_H W) memB (o + 10 + Z.of_nat j) = Some (cp_v fr j))
  by (clear HS; intros j Hj; rewrite Hfrc by (rewrite ?Hes; lia); apply OA; exact Hj);
assert (HKC : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp1 - 4096 <= a < sp1) \/ (o + 4 <= a < o + 10)) ->
  aview SEGS (w_H W) memB a = aview SEGS (w_H W) mT a)
  by (intros a Ha Hna; apply Hfrc; [exact Ha | clear - Hna; lia | rewrite Hes; clear - Hna; lia]);
let KP' := fresh "KP" in
pose proof (KOWN mT memB (fun a => (sp1 - 4096 <= a < sp1) \/ (o + 4 <= a < o + 10)) ltac:(acc_hz Hsp1r WS) KP HKC Hpres2) as KP';
clear KP; rename KP' into KP end.
clear OZ1 OA HKC Heff. rename OA' into OA.
jafter_call_keep_hi HS 776%nat rB (mrestrict (w_H W) memB) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
{ clear HS HS2. cbn [ms_mem restrict]. pose proof KP as (_ & _ & _ & _ & _ & KP6). repeat apply Forall_cons; try apply Forall_nil.
  - apply (pz_region_kept _ _ _ _ 529%nat (SB + F / 8)); [rewrite E529; apply unsigned_lit_small; unfold SB; lia | intros a Ha; unfold SB in Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; lia].
  - apply (pz_region_kept _ _ _ _ 516%nat F); [rewrite RF; apply unsigned_lit_small; lia | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; lia].
  - apply (pz_region_kept _ _ _ _ 33%nat sp1); [rewrite (AGX 33%nat) by lia; exact B33 | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; apply KP6; lia].
  - apply (pz_region_kept _ _ _ _ 2%nat sp); [rewrite (AGX 2%nat) by lia; exact Usp | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; apply KP6; lia].
  - apply (pz_region_kept _ _ _ _ 10%nat f); [rewrite (AGX 10%nat) by lia; exact B10 | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS Hfrc HP2 Hpres2 Hb0'; rename HS2 into HS.
pz_rebase HS AGX.
clear SHOK. pose proof (SHOKF _ memB _ ltac:(rewrite (AGX 10%nat) by lia; exact E10) ltac:(rewrite (AGX 12%nat) by lia; exact E12)
  ltac:(rewrite (AGX 32%nat) by lia; exact E32) (proj1 HJX) KP) as SHOK.
clear HJ2. rename HJX into HJ2.
(* 4. The bcmp wrapper (through the 4-byte jump __interceptor_trampoline_bcmp) compares f[0..5] with .str.4
   (six 0xff bytes) at 0x8756c. *)
paj_run_tok RUN HS HJ2 SHOK PZspan; [awrFL_with ltac:(idtac; pz_awr_hd) AGX fpos F EF|].
acc_kept KOWN (fun a => sp1 <= a < sp) HKR Hsp1r WS.
lazymatch type of HKR with forall a, _ -> _ -> aview _ _ ?mB a = aview _ _ ?mA a =>
assert (OZ2' : forall j, 0 <= j < 4 \/ 16 <= j < 36 -> aview SEGS (w_H W) mB (o + j) = Some 0)
  by (clear HS; intros j Hj; rewrite HKR; [apply OZ2; exact Hj | lia | cbv beta; lia]);
assert (OA' : forall j, (j < 6)%nat -> aview SEGS (w_H W) mB (o + 10 + Z.of_nat j) = Some (cp_v fr j))
  by (clear HS; intros j Hj; rewrite HKR; [apply OA; exact Hj | lia | cbv beta; lia]);
assert (OB' : forall j, (j < 6)%nat -> aview SEGS (w_H W) mB (o + 4 + Z.of_nat j) = Some (cp_v fr (6 + j)))
  by (clear HS; intros j Hj; rewrite HKR; [apply OB; exact Hj | lia | cbv beta; lia]) end.
clear OZ2 OA OB HKR HF HFr HG. rename OZ2' into OZ2. rename OA' into OA. rename OB' into OB. acc_rebase HS AGX.
prreg HS (10%bv : bv 5) Rc0. prreg HS (11%bv : bv 5) Rc1. prreg HS (12%bv : bv 5) Rc2.
prreg HS (1%bv : bv 5) Rcra. prreg HS (2%bv : bv 5) Rcsp. prreg HS (3%bv : bv 5) Rcgp. prreg HS (4%bv : bv 5) Rctp.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (HspT3 : spZ (ms_regs msX) = sp1) by (unfold spZ; rewrite Rcsp, (AGX 33%nat), B33 by lia; reflexivity);
  assert (RODX : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem msX)));
  [ pose proof KP as (_ & _ & K3 & _); intros a Hro Ho He; rewrite (K3 a); [exact (HROD a Hro Ho He) | | exact Ho | exact He];
    destruct Hro as [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hg)]
  | pose proof (HBC_VAL (w_H W) (ms_mem msX) RODX) as HY;
    assert (FBH : forall i, (i < 6)%nat -> aview SEGS (w_H W) (ms_mem msX) (f + Z.of_nat i) = Some (cp_v fr i))
      by (clear HS; intros i Hi; apply (FB _ KP); lia) ] end.
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mT ?dT _ =>
destruct (ro_read_ok_glob SEGS B G lyc S2 W mT dT (VAL (A_OBJ OBJ_BCAST)) 7 (VAL (A_OBJ OBJ_BCAST)) 6 HGM HG15 HIMGSH (proj1 HJ2)
  ltac:(clear HS; lia) ltac:(clear HS; lia) ltac:(clear HS; lia) ltac:(clear HS; lia) ltac:(clear HS; lia)) as [HRY HHY] end.
pmkst HS.
eapply SRr_bind.
{ clear HS. lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA DS___interceptor_trampoline_bcmp) (ABCMP fq) W rT mT
    STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 dT k f (VAL (A_OBJ OBJ_BCAST)) 6 (sp1 - sp0) _ HJ2) end.
  - rewrite Rc0, (AGX 10%nat), E10 by lia. reflexivity.
  - rewrite Rc1, (AGX 299%nat) by lia. exact (EOB 58%nat ltac:(lia)).
  - rewrite Rc2. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite HspT3. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite Rcgp, (AGX 3%nat), (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
  - rewrite Rctp, (AGX 4%nat), (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
  - exact Rcra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [apply (FBN _ KP); lia | rewrite HspT3, Hes; acc_lia].
  - intros a Ha. split; [replace a with (VAL (A_OBJ OBJ_BCAST) + (a - VAL (A_OBJ OBJ_BCAST))) by lia; rewrite HY by lia; discriminate
    | rewrite HspT3, Hes; lia].
  - intros a Ha. rewrite Hes. acc_lia.
  - intros a Ha. rewrite Hes. lia.
  - clear - Hfam. unfold amem_range in *. lia.
  - unfold amem_range, kLowMemEnd. left. lia.
  - intros x Hx. apply (RAF _ _ (proj1 HJ2) KP). lia.
  - intros _. apply (HUF _ _ f 6 (proj1 HJ2)); lia.
  - exact HRY.
  - intros _. exact HHY. }
cbv beta. intros W2 c2 _ (-> & rC & memC & mdC & vC & -> & HJX & HP2 & Hc0' & Hcmp & Hfrc & Hpres2).
assert (Hbc : vC = Z_to_bv 64 0 <-> cp_bcast fr = true) by exact (iff_trans Hcmp (acc_bcast_iff fr _ _ f (VAL (A_OBJ OBJ_BCAST)) FBH HY)).
lazymatch type of Hfrc with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mT a =>
assert (OZ3 : forall j, 0 <= j < 4 \/ 16 <= j < 36 -> aview SEGS (w_H W) memC (o + j) = Some 0)
  by (clear HS; intros j Hj; rewrite Hfrc by (rewrite ?Hes; lia); apply OZ2; exact Hj);
assert (OA' : forall j, (j < 6)%nat -> aview SEGS (w_H W) memC (o + 10 + Z.of_nat j) = Some (cp_v fr j))
  by (clear HS; intros j Hj; rewrite Hfrc by (rewrite ?Hes; lia); apply OA; exact Hj);
assert (OB' : forall j, (j < 6)%nat -> aview SEGS (w_H W) memC (o + 4 + Z.of_nat j) = Some (cp_v fr (6 + j)))
  by (clear HS; intros j Hj; rewrite Hfrc by (rewrite ?Hes; lia); apply OB; exact Hj);
assert (HKC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> aview SEGS (w_H W) memC a = aview SEGS (w_H W) mT a)
  by (intros a Ha Hna; apply Hfrc; [exact Ha | rewrite Hes; clear - Hna; lia]);
let KP' := fresh "KP" in
pose proof (KOWN mT memC (fun a => sp1 - 8192 <= a < sp1) ltac:(acc_hz Hsp1r WS) KP HKC Hpres2) as KP';
clear KP; rename KP' into KP end.
clear OZ2 OA OB HKC. rename OA' into OA. rename OB' into OB.
jafter_call_keep_hi HS 792%nat rC (mrestrict (w_H W) memC) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
{ clear HS HS2. cbn [ms_mem restrict]. pose proof KP as (_ & _ & _ & _ & _ & KP6). repeat apply Forall_cons; try apply Forall_nil.
  - apply (pz_region_kept _ _ _ _ 529%nat (SB + F / 8)); [rewrite E529; apply unsigned_lit_small; unfold SB; lia | intros a Ha; unfold SB in Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; lia].
  - apply (pz_region_kept _ _ _ _ 516%nat F); [rewrite RF; apply unsigned_lit_small; lia | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; lia].
  - apply (pz_region_kept _ _ _ _ 33%nat sp1); [rewrite (AGX 33%nat) by lia; exact B33 | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; apply KP6; lia].
  - apply (pz_region_kept _ _ _ _ 2%nat sp); [rewrite (AGX 2%nat) by lia; exact Usp | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; apply KP6; lia].
  - apply (pz_region_kept _ _ _ _ 10%nat f); [rewrite (AGX 10%nat) by lia; exact B10 | intros a Ha; apply Hfrc; rewrite ?Hes; acc_lia | intros a Ha; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS Hfrc HP2 Hpres2; rename HS2 into HS.
pz_rebase HS AGX.
clear HJ2. rename HJX into HJ2.
(* 5. The out struct comes back as a region (pz_out_cutB), then the join to cut B (atom 640 = the bcmp result). *)
assert (Hopres4 : forall i, 0 <= i < 36 -> apresent (w_H W) memC (o + i)) by (intros i Hi; apply (HOp _ _ HJ2); lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (ROK : region_ok SEGS Ev (ms_mem msx) (YP09.mkRegion (Some 12%nat) 0 36 0 36 pz_out_cutB));
[| assert (RDJ : all_disjoint Ev (YP09.mkRegion (Some 12%nat) 0 36 0 36 pz_out_cutB) (ss_mem ssx))] end.
{ clear HS. cbn [ms_mem restrict mkst]. apply (acc_out_cutB _ (w_H W) memC o fr).
  - rewrite (AGX 12%nat) by lia. exact B12.
  - lia.
  - lia.
  - exact Hopres4.
  - intros i Hi. split.
    + rewrite (AGX (46 + i)%nat) by lia. replace (46 + i)%nat with (40 + (6 + i))%nat by lia. apply EFB. lia.
    + rewrite (AGX (40 + i)%nat) by lia. apply EFB. lia.
  - exact OZ3.
  - exact OB.
  - exact OA. }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
  cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. pz_bases.
  revert Hslo Hceil Hwin WS C1 Hsp1r Hsp0 Ho4096 Ho47 Howin Hosh' Hf0 Hf47 Hdfo HF4096 HFceil HF8lo HF8hi HsepO Hslo2.
  unfold SB. clear. intros. repeat split; acc_lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 12%nat) 0 36 0 36 pz_out_cutB) HS ltac:(vm_compute; reflexivity) ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
ra_join HS ss_cutB 640%nat pz_deadB idtac.
ra_join_val HS 640%nat 0%nat Hc0' E640.
pz_rebase HS AGX.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => apply (HcB Hbig Ev) end.
- split; [assumption|]. split; [exact AGX|]. split; [exact RF|]. split; [exact E528|]. split; [exact E529|].
  split; [exact HJ2 | exact KP].
- exact HS.
- apply (SHOKF _ _ _ ltac:(rewrite (AGX 10%nat) by lia; exact E10) ltac:(rewrite (AGX 12%nat) by lia; exact E12)
    ltac:(rewrite (AGX 32%nat) by lia; exact E32) (proj1 HJ2) KP).
- exact Hhdr.
- rewrite E640. exact Hbc.
Qed.
End d.
End b.
