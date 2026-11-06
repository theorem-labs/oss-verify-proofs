(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* Modified by Theorem Labs, 2026-10: copied by path from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParseAcc.v (a working branch 603e40683a4) for libreac/fuzz_scene's asan-ubsan walk; the module paths and the listing's names changed (Grant* -> Scene*, GS___ -> SS___, grant_listing -> scene_listing, KindOfLink1 -> P_kind_of_link1; MERGE-GATES 6o: YCbq from lib.AU), the sink head is passed by name to the cut predicates (gate 6h), and every pc in a comment is fuzz_scene.asan-ubsan's (sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f): reac_ctrl_parse = 0x84028, cut M = 0x84168, cut B = 0x84224. The donor file carries no copyright and no SPDX line; the four lines above are its siblings' (CtrlParseNone.v, CtrlParseMid.v), added on a review ruling of 2026-10-29 so that no file enters this tree without one. *)
(* reac_ctrl_parse, the walk from cut M (0x84168) to cut B (0x84224) on the path the header check accepts:
   the two memcpys of the addresses and the bcmp wrapper against .str.4 ("\xff" x 6).
   UBSan guards between the two cuts, each a branch to the one trap, unimp @0x84824 (f = atom 10 = s5,
   o = atom 12 = s3 = s4):
     G01 beqz s5 @0x84170, and G02 bgeu s5,a0 @0x84178 (li a0,-12 @0x84174), before the load of frame[12];
     G03 bltu a0,s5 @0x841a0 (li a0,-14 @0x8419c), before the load of frame[13];
     G04 bnez a0 @0x841c8 (andi a0,s3,3 @0x841c4), before the first memcpy;
     G05 bltu a1,a0 @0x841f0 (addi a1,s5,6 @0x841e8; li a0,7 @0x841ec), after it.
   No step of the proof names them. Cut M's facts give atoms 10 and 12 the fact mkAF 4096 0x7fffff800000 3
   (CtrlParseLib.ss_cutM), and with them the engine (PaSym, a Branch step) decides each guard by decide_cond2:
   f's unsigned range [4096, 0x7fffff800000] is disjoint from 0 and lies below 2^64 - 14 and 2^64 - 12, and
   f + 6 is not below 7; for the andi, s_and_ptr (YP0m) makes s_alu ALU_AND (SOff 12 0) (SLit 3) the literal 0,
   because o is 2^3-aligned and 3 < 2^3. So each run below goes past the guards to the next undecided branch or
   call, exactly as in the donor's asan walk, and no cut predicate carries a fact a guard would have to give it.
   Two differences from the donor, both code motion, neither visible in the proof's steps: the first memcpy's
   destination is computed in a0 (mv a0,s10 @0x841cc; beqz s4 @0x841d0; mv a0,s4 @0x841d4; addi a0,a0,10
   @0x841d8) where the donor uses s6, and s6 is set to o only after G05 (@0x841f4 .. @0x841fc) and to o + 16
   before the bcmp call (addi s6,s6,16 @0x8420c) -- which is why cut B's s6 is SOff 12 16 (CtrlParseLib.ss_cutB),
   the one constant of the cut that differs from the asan twin's. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow PaJournal SceneSyms SceneList ScenePa ScenePaLib.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import SceneBase YC81 YC4b YC1g YC1h YC45 YC85 SceneFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_reac_ctrl_parse CtrlParseLib P_kind_of_link1 SceneRo ACj1 SceneACja.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import CtrlParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
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
| unbox; lia ].
(* The windows a run may write are inside Zs: carry acall_kept over the run (KOWN, pz_kept_own specialised to
   this walk), and give HKR, the run's memory outside Zs unchanged. *)
Local Ltac acc_hz Hs1 WSx := let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbv beta in Ha; unfold pz_nf; clear - Ha Hs1 WSx; lia.
Local Ltac acc_kept KOWN Zs HKR Hs1 WSx :=
lazymatch goal with HFr : frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) |- _ =>
lazymatch goal with HG : mem_grows (mrestrict _ mA) (mrestrict _ mB) |- _ =>
let Hw1 := fresh "Hw1" in
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi -> Zs a)
  by (pz_win_tac ltac:(fun H => acc_bases_in H; clear - H Hs1));
lazymatch goal with KP : acall_kept ?sg _ _ _ _ _ _ _ _ _ _ |- _ =>
pose proof (kept_of_frame (segs := sg) _ _ _ _ _ _ HFr Hw1) as HKR;
let KP' := fresh "KP" in
pose proof (KOWN mA mB Zs ltac:(acc_hz Hs1 WSx) KP HKR (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
clear KP Hw1; rename KP' into KP end end end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg scene_listing}.
Context {RO : ro_below_ofl (@pa_segs _ scene_listing PI) (@pa_relro_lo _ scene_listing PI) (@pa_relro_hi _ scene_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
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
Lemma pz_segAcc : forall B G, pz_rt (SK := SK) B G -> forall c, pz_ok (SK := SK) B c -> pz_cutB_spec (SK := SK) B c ->
pz_cutM_case (SK := SK) B c (cp_hdr (cx_n c) (cx_fr c) = true).
Proof.
intros B G RT c Hok HcB E ms md Hcur HS SHOK Hhdr.
unfold pz_cutB_spec in HcB.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_std.
pose proof (proj1 (cp_hdr_spec n fr) Hhdr) as (Hn50 & Hf12 & Hf13).
pose (RUN := paj_run B LAWS). pose (BR := paj_branch (PI := PI)).
box HFapp. box HsepF. box HsepO. box Hdfo.
(* Facts about the two caller objects f and o, used at every step. *)
assert (Hfap : f + 50 <= kLowShadowBeg \/ kHighMemBeg <= f /\ f + 50 <= ASAN_CEIL) by (unfold in_app in Hfapp; lia).
assert (Hoap : o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o /\ o + 36 <= ASAN_CEIL) by (unfold in_app in Hoapp; lia).
box Hfap. box Hoap.
assert (Hfam : amem_range f 50) by (apply (amem_range_sub_app (frame_addr lyc cf pf) (fs_frame_bytes cf)); [exact Hfapp | exact Hfceil | lia | lia | lia]).
assert (Hoam : amem_range o 36) by (apply (amem_range_sub_app (frame_addr lyc co po) (fs_frame_bytes co)); [exact Hoapp | exact Hoceil | lia | lia | lia]).
assert (Hfam' : f + 50 <= 140737488355327) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hfam; lia).
assert (Hoam' : o + 36 <= 140737488355327) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hoam; lia).
pose proof Hoapp as Hoapp'. pose proof Hfapp as Hfapp'. unfold in_app, kLowShadowBeg, kHighMemBeg in Hoapp', Hfapp'.
box Hoapp'. box Hfapp'.
assert (FB : forall memX, acall_kept SEGS B lyc Sc W memc W memX (sp - TPARSE_STK) sp (fun a => o <= a < o + 36) ->
  forall i, (i < 50)%nat -> aview SEGS (w_H W) memX (f + Z.of_nat i) = Some (cp_v fr i)).
{ intros memX KPX i Hi. rewrite (pz_kept_frame_byte B lyc Sc W memc memX _ _ _ cf pf (f + Z.of_nat i) KPX Hfin ltac:(lia) ltac:(cbv beta; acc_lia)).
  exact (Hfr i Hi). }
assert (FBN : forall memX, acall_kept SEGS B lyc Sc W memc W memX (sp - TPARSE_STK) sp (fun a => o <= a < o + 36) ->
  forall a, f <= a < f + 50 -> aview SEGS (w_H W) memX a <> None).
{ intros memX KPX a Ha. replace a with (f + Z.of_nat (Z.to_nat (a - f))) by lia. rewrite (FB memX KPX) by lia. discriminate. }
assert (RAF : forall memX, acall_kept SEGS B lyc Sc W memc W memX (sp - TPARSE_STK) sp (fun a => o <= a < o + 36) ->
  range_addressable (aview SEGS (w_H W) memX) SHADOW_OFF f 50).
{ intros memX KPX. apply (pz_kept_ra B LAWS lyc Sc W memc mdc memX _ _ _ cf pf f 50 HAR KPX Hfin Hflo Hfhi); [|exact HRf].
  intros x Hx Hc. cbv beta in Hc. apply (pz_sh_app x (frame_addr lyc co po) (fs_frame_bytes co)); [lia | exact Hoapp | lia]. }
assert (RAO : forall memX, acall_kept SEGS B lyc Sc W memc W memX (sp - TPARSE_STK) sp (fun a => o <= a < o + 36) ->
  range_addressable (aview SEGS (w_H W) memX) SHADOW_OFF o 36).
{ intros memX KPX. apply (pz_kept_ra B LAWS lyc Sc W memc mdc memX _ _ _ co po o 36 HAR KPX Hoin Holo Hohi); [|exact HRo].
  intros x Hx Hc. cbv beta in Hc. apply (pz_sh_app x (frame_addr lyc co po) (fs_frame_bytes co)); [lia | exact Hoapp | lia]. }
assert (SHOKF : forall Ex memX, ew Ex 10 = Z_to_bv 64 f -> ew Ex 12 = Z_to_bv 64 o -> ew Ex 32 = Z_to_bv 64 SB ->
  acall_kept SEGS B lyc Sc W memc W memX (sp - TPARSE_STK) sp (fun a => o <= a < o + 36) ->
  sh_ok SEGS PZx PZ_SH Ex (mrestrict (w_H W) memX)).
{ intros Ex memX X10 X12 X32 KPX. apply (pz_shok Ex (w_H W) memX f o X10 X12 X32); [lia | exact Hfap | lia | exact Hoap | exact (RAF memX KPX) | exact (RAO memX KPX)]. }
assert (KOWN : forall memX memY (Zs : Z -> Prop),
  (forall a, Zs a -> (sp - TPARSE_STK <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) ->
  acall_kept SEGS B lyc Sc W memc W memX (sp - TPARSE_STK) sp (fun a => o <= a < o + 36) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) memY a = aview SEGS (w_H W) memX a) ->
  (forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
  acall_kept SEGS B lyc Sc W memc W memY (sp - TPARSE_STK) sp (fun a => o <= a < o + 36)).
{ intros memX memY Zs HZ KPX Hkp Hgr.
  exact (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ memX memY (sp - TPARSE_STK) sp o fpos F FL Zs co po
    HAR HARc Hfrs2 Eab EF EFL FFL ltac:(lia) ltac:(lia) Hoin Holo Hohi HZ KPX Hkp Hgr). }
(* 1. The header checks: n >= 50 (0x8416c), f[12] = 0x88 (0x84198), f[13] = 0x19 (0x841c0); the shadow checks of
   f + 12 and f + 13 (0x8418c, 0x841b4, to the error path at 0x84828 / 0x84834) are taken by the run from sh_ok.
   The same runs pass G01 and G02 (before the f[12] branch) and G03 (before the f[13] branch). *)
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
(* 2. checked_memcpy(o + 10, f, 6) at 0x841e4. The destination is computed in a0, not in s6: s4 = o is not 0,
   so the branch at 0x841d0 is decided by o's fact and a0 = o + 10. This run also passes G04. The out struct is
   dropped from the state; its bytes are carried as facts (OZ1, OA). *)
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
  eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA SS___asan_memcpy) AMEMCPY W rT mT
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
  - intros a Ha. split; [rewrite Eab; apply pz_awr_cons; apply HOW; lia | rewrite Hes; lia].
  - apply (amem_range_sub_app (frame_addr lyc co po) (fs_frame_bytes co)); [exact Hoapp | exact Hoceil | lia | lia | lia].
  - intros x Hx. apply (RAO _ KP). lia.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W _ _ co po (o + 10) 6 (proj1 HJ2) (HfinS2 co po Hoin)); lia.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [apply (FBN _ KP); lia | rewrite HspT, Hes; lia]. }
    split; [acc_lia|]. split.
    { apply (amem_range_sub_app (frame_addr lyc cf pf) (fs_frame_bytes cf)); [exact Hfapp | exact Hfceil | lia | lia | lia]. }
    split; [intros x Hx; apply (RAF _ KP); lia|].
    intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W _ _ cf pf f 6 (proj1 HJ2) (HfinS2 cf pf Hfin)); lia. }
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
clear SHOK. pose proof (SHOKF _ memA ltac:(rewrite (AGX 10%nat) by lia; exact E10) ltac:(rewrite (AGX 12%nat) by lia; exact E12)
  ltac:(rewrite (AGX 32%nat) by lia; exact E32) KP) as SHOK.
clear HJ2. rename HJX into HJ2.
(* 3. checked_memcpy(o + 4, f + 6, 6) at 0x84208: the source a1 = f + 6 is set @0x841e8, the destination from
   s6 (mv s6,s10 @0x841f4; beqz s4 @0x841f8; mv s6,s4 @0x841fc; addi a0,s6,4 @0x84200). This run passes G05. *)
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
  eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA SS___asan_memcpy) AMEMCPY W rT mT
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
  - intros a Ha. split; [rewrite Eab; apply pz_awr_cons; apply HOW; lia | rewrite Hes; lia].
  - apply (amem_range_sub_app (frame_addr lyc co po) (fs_frame_bytes co)); [exact Hoapp | exact Hoceil | lia | lia | lia].
  - intros x Hx. apply (RAO _ KP). lia.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W _ _ co po (o + 4) 6 (proj1 HJ2) (HfinS2 co po Hoin)); lia.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [apply (FBN _ KP); lia | rewrite HspT2, Hes; lia]. }
    split; [acc_lia|]. split.
    { apply (amem_range_sub_app (frame_addr lyc cf pf) (fs_frame_bytes cf)); [exact Hfapp | exact Hfceil | lia | lia | lia]. }
    split; [intros x Hx; apply (RAF _ KP); lia|].
    intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W _ _ cf pf (f + 6) 6 (proj1 HJ2) (HfinS2 cf pf Hfin)); lia. }
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
clear SHOK. pose proof (SHOKF _ memB ltac:(rewrite (AGX 10%nat) by lia; exact E10) ltac:(rewrite (AGX 12%nat) by lia; exact E12)
  ltac:(rewrite (AGX 32%nat) by lia; exact E32) KP) as SHOK.
clear HJ2. rename HJX into HJ2.
(* 4. The bcmp wrapper (through the 4-byte jump __interceptor_trampoline_bcmp) compares f[0..5] with .str.4
   (six 0xff bytes, listing object 15: auipc a0 @0x84210, addi a1,a0,-976 @0x84214) at 0x84220. In the same run
   s6 becomes o + 16 (addi s6,s6,16 @0x8420c), which is cut B's value of s6. *)
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
(* scene's SceneRo.v states IMG_LO and IMG_HI as Definitions, where grant's GrantRo.v gives IMG_HI as a
   parsing-only name for IMG_TOP (the same number, 0x5f9000): so the last side condition below unfolds
   IMG_HI before lia reads HBC_RNG, and the bcmp call's `0 <= y` and `amem_range y 6` take the object's
   lower bound from pa_val_range, which HBC_RNG's now-folded IMG_LO no longer gives lia. *)
pose proof (pa_val_range (A_OBJ OBJ_BCAST)) as HBCVR.
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mT ?dT _ =>
destruct (ro_read_ok_glob SEGS B G lyc S2 W mT dT (VAL (A_OBJ OBJ_BCAST)) 7 (VAL (A_OBJ OBJ_BCAST)) 6 HGM HG15 HIMGSH (proj1 HJ2)
  ltac:(clear HS; lia) ltac:(clear HS; lia) ltac:(clear HS; lia) ltac:(clear HS; lia) ltac:(clear HS; unfold IMG_HI; lia)) as [HRY HHY] end.
pmkst HS.
eapply SRr_bind.
{ clear HS. lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA SS___interceptor_trampoline_bcmp) ABCMP W rT mT
    STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 dT k f (VAL (A_OBJ OBJ_BCAST)) 6 (sp1 - sp0) _ HJ2) end.
  - rewrite Rc0, (AGX 10%nat), E10 by lia. reflexivity.
  - rewrite Rc1, (AGX 256%nat) by lia. exact (EOB 15%nat ltac:(lia)).
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
  - intros a Ha. split; [apply (FBN _ KP); lia | rewrite HspT3, Hes; lia].
  - intros a Ha. split; [replace a with (VAL (A_OBJ OBJ_BCAST) + (a - VAL (A_OBJ OBJ_BCAST))) by lia; rewrite HY by lia; discriminate
    | rewrite HspT3, Hes; lia].
  - intros a Ha. rewrite Hes. lia.
  - intros a Ha. rewrite Hes. lia.
  - apply (amem_range_sub_app (frame_addr lyc cf pf) (fs_frame_bytes cf)); [exact Hfapp | exact Hfceil | lia | lia | lia].
  - unfold amem_range, kLowMemEnd. left. lia.
  - intros x Hx. apply (RAF _ KP). lia.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W _ _ cf pf f 6 (proj1 HJ2) (HfinS2 cf pf Hfin)); lia.
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
destruct (al_frames _ _ LAWS _ _ _ _ _ co po (proj1 HJ2) (HfinS2 co po Hoin)) as (_ & _ & Hopres4 & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
assert (ROK : region_ok SEGS Ev (ms_mem msx) (YP09.mkRegion (Some 12%nat) 0 36 0 36 pz_out_cutB));
[| assert (RDJ : all_disjoint Ev (YP09.mkRegion (Some 12%nat) 0 36 0 36 pz_out_cutB) (ss_mem ssx))] end.
{ clear HS. cbn [ms_mem restrict mkst]. apply (acc_out_cutB _ (w_H W) memC o fr).
  - rewrite (AGX 12%nat) by lia. exact B12.
  - lia.
  - lia.
  - intros i Hi. exact (proj1 (Hopres4 (o + i) ltac:(lia))).
  - intros i Hi. split.
    + rewrite (AGX (46 + i)%nat) by lia. replace (46 + i)%nat with (40 + (6 + i))%nat by lia. apply EFB. lia.
    + rewrite (AGX (40 + i)%nat) by lia. apply EFB. lia.
  - exact OZ3.
  - exact OB.
  - exact OA. }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
  cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. pz_bases.
  revert Hslo Hceil Hwin WS C1 Hsp1r Hsp0 Holo Hohi Hoceil Ho4096 Hflo Hfhi Hfceil Hf4096 HF4096 HFceil HF8lo HF8hi HsepO Hoapp' Hdfo.
  unfold SB. clear. intros. repeat split; acc_lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 12%nat) 0 36 0 36 pz_out_cutB) HS ltac:(vm_compute; reflexivity) ROK RDJ) as HS' end.
clear HS ROK RDJ; rename HS' into HS. pz_norm HS.
ra_join HS ss_cutB 640%nat pz_deadB idtac.
ra_join_val HS 640%nat 0%nat Hc0' E640.
pz_rebase HS AGX.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => apply (HcB Ev) end.
- split; [assumption|]. split; [exact AGX|]. split; [exact RF|]. split; [exact E528|]. split; [exact E529|].
  split; [exact HJ2 | exact KP].
- exact HS.
- apply SHOKF; [rewrite (AGX 10%nat) by lia; exact E10 | rewrite (AGX 12%nat) by lia; exact E12 | rewrite (AGX 32%nat) by lia; exact E32 | exact KP].
- exact Hhdr.
- rewrite E640. exact Hbc.
Qed.
End d.
End b.
