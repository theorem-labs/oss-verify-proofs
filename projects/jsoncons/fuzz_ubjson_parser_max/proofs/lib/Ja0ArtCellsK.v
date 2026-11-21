(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added section variables such as mbase, stdin, gid, groups, net, kb, execfn and apc, passed them to SINV, argH and AH, and wrote art_lit1, art_lit and cell0_cat as plain statements, dropping the TCodec name table; the launch input takes its SIGPIPE disposition as a variable sdf; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0ArtCellsK.v, lines 76-86, 94-95, 107-108, 116-117. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ja0DefsK Ja0PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Definition ART_LITW : list (Z * nat * Z) :=
[
(1275544 + 40, 4%nat, 0xffffffff); (1275544 + 56, 1%nat, 0); (0x10400, 8%nat, 0xafffff00000fffff); (0x132618, 8%nat, 0x1ca7a0); (0x1ca7a0, 8%nat, 4096);
(0x1cc828 + 260, 1%nat, 0); (0x1cc828 + 144, 8%nat, 0);
(0x132638, 8%nat, 0x13acf8); (0x13acf8, 8%nat, 0x7fff8000); (0x132640, 8%nat, 0x13b9e8); (0x13b9e8, 8%nat, 0); (0x132648, 8%nat, 0x13b9f0); (0x13b9f0, 8%nat, 0);
(0x132650, 8%nat, 0x13b9e0); (0x13b9e0, 8%nat, 2 ^ 47 - 1); (0x132630, 8%nat, 0x1384f8); (0x1384f8 + 78, 1%nat, 1); (0x132658, 8%nat, 0x134648); (0x134648, 8%nat, 0x124db0);
(0x132628, 8%nat, 0x1cc828); (0x1cc828 + 120, 8%nat, 18446744073709551615); (0x13a55c, 1%nat, 1);
(0x13a560, 1%nat, 1); (0x13a564, 4%nat, 0); (0x66ed80 - 88, 8%nat, 0x690238);
(0x10418, 8%nat, 0x218a392cd3d5dbf); (0x10494, 1%nat, 3); (0x10358, 8%nat, 0xcc6e96b9cc6e96b9); (0x10598, 1%nat, 4); (0x105c1, 1%nat, 11);
(0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10320, 8%nat, 0x35253c9ade8f4ca8); (0x103f8, 8%nat, 0x9747b28c9747b28c);
(0x13b9d8, 1%nat, 1); (0x1bcf62, 1%nat, 0); (1275544 + 3616, 8%nat, 2 ^ 40); (1275544 + 3624, 2%nat, 16); (1275544 + 3626, 2%nat, 2048);
(0x1cc7c0, 8%nat, 0); (0x1cc7c8, 8%nat, 0); (0x1384f8 + 44, 4%nat, 4096); (0x1384f8 + 48, 4%nat, 0); (0x1384f8 + 52, 4%nat, 190); (0x1384f8 + 85, 1%nat, 1);
(0x133298, 8%nat, 0x10); (0x13b9fc, 4%nat, 30); (0x1cc828 + 34, 1%nat, 1); (0x137970 + 80, 8%nat, 2 ^ 20); (0x137970 + 64, 8%nat, 2 ^ 28);
(0x1345f0, 8%nat, 0x1254d0); (0x134480, 8%nat, 0x1248b0);
(0x66ed80 + 0x10, 4%nat, 0);
(1275544 + 64, 8%nat, 4096); (1275544 + 64 + 56, 8%nat, 0); (1275544 + 64 + 48, 8%nat, 0); (1275544 + 64 + 616, 1%nat, 0);
(0x137970 + 160, 8%nat, 0); (0x137970 + 168, 8%nat, 0); (0x137970 + 176, 8%nat, 0); (0x137970 + 184, 8%nat, 0); (0x137970 + 152, 1%nat, 0); (0x137970 + 153, 1%nat, 0);
(0x1ca788, 1%nat, 0); (0x1ca789, 1%nat, 0);
(0x61cbd8, 4%nat, 1);
(1275544 + 64 + 617, 3%nat, 0); (0x137970 + 154, 2%nat, 0); (0x1ca788, 4%nat, 0);
(0x132620, 8%nat, 0x134680); (0x134680, 8%nat, 0x1a50c); (0x13b9d9, 1%nat, 1); (0x1cc923, 1%nat, 1); (0x1cc8b1, 1%nat, 1); (0x1cc828 + 84, 1%nat, 1);
(0x1ca798, 4%nat, 0); (0x13ad00, 4%nat, 1); (0x134640, 8%nat, 0x1249ac);
(0x137970 + 72, 8%nat, 0xe666661);
(0x132678, 8%nat, 1);
(0x1345d8, 8%nat, 0x10b84c); (0x1331a0, 8%nat, 0x13b9d9); (0x134538, 8%nat, 0x125990); (0x132688, 8%nat, 0x1ca798); (0x133440, 8%nat, 8);
(0x1cc87c, 1%nat, 1); (0x134490, 8%nat, 0x12b3b0); (0x134498, 8%nat, 0x11bdac); (0x1344c0, 8%nat, 0x1224a8); (0x1344c8, 8%nat, 0x11c1c4);
(0x134448, 8%nat, 0x134448); (0x137640, 8%nat, 1); (0x137690, 1%nat, 0); (0x138510, 4%nat, 1); (0x1385b0, 8%nat, 0); (0x1ccba0, 1%nat, 0);
(0x66ed78, 8%nat, 0x66eda0); (0x66eda8, 8%nat, 0x66f580);
(0x134450, 8%nat, 0x125294); (0x134518, 8%nat, 0x11355c); (0x134520, 8%nat, 0x1251fc);
(0x10498, 1%nat, 4);
(0x138514, 1%nat, 0);
(0x1345e8, 8%nat, 0x113744);
(0x138558, 1%nat, 1);
(0x134470, 8%nat, 0x12497c); (0x1cc926, 1%nat, 1); (0x1cc927, 1%nat, 1) ].
Definition chk_lit1 (k : list kentry) (c : Z * nat * Z) : bool :=
let '(a, w, v) := c in
(chk_sub k a w v || chk_img ASEGS0 ASAN0 k a w v || (chk_zero k (ELit 0) a (Z.of_nat w) && Z.eqb v 0 && Nat.leb w 8 && Z.leb 0 a))%bool.
Definition art_lits_chk (cs : acs) : bool := forallb (chk_lit1 (kn cs)) ART_LITW.
Section Lits.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Variable mbase : word.
Variable stdin : InputStream.
Variable gid : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abrt : bool.
Variable ur : InputStream.
Variable kb : KernelBuild.
Variable execfn : list byte.
Variable sdf : bool.
Variable apc : N.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
#[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Let AH := argH0_high sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva.
Lemma art_lit1 : forall E cs R FULL model c, CSOK E cs R FULL model -> chk_lit1 (kn cs) c = true ->
cell ASEGS0 FULL (fst (fst c)) (snd (fst c)) (snd c).
Proof.
intros E cs R FULL model [[a w] v] HC H. cbn [fst snd]. unfold chk_lit1 in H. unfold cell.
apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
- exact (hc_sub ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model a w v HC H).
- exact (hc_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model a w v HC H).
- apply andb_prop in H as [H Ha]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [H Hv].
apply Z.eqb_eq in Hv. subst v. apply Nat.leb_le in Hw. apply Z.leb_le in Ha.
apply (hc_zero_cell ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model (ELit 0) a (Z.of_nat w) HC H a w Hw);
unfold uE; cbn [edenot]; rewrite u64_lit by lia; lia.
Qed.
Lemma art_lit : forall E cs R FULL model, CSOK E cs R FULL model -> art_lits_chk cs = true ->
forall a w v, In (a, w, v) ART_LITW -> cell ASEGS0 FULL a w v.
Proof.
intros E cs R FULL model HC H a w v Hin.
exact (art_lit1 E cs R FULL model (a, w, v) HC (proj1 (forallb_forall _ _) H _ Hin)).
Qed.
End Lits.
Lemma cell0_cat : forall (M : word -> option byte) a (w1 w2 : nat), 0 <= a -> a + Z.of_nat w1 < 2 ^ 64 -> (w1 + w2 <= 8)%nat ->
cell ASEGS0 M a w1 0 -> cell ASEGS0 M (a + Z.of_nat w1) w2 0 -> cell ASEGS0 M a (w1 + w2) 0.
Proof.
intros M a w1 w2 Ha Hn Hw H1 H2. unfold cell in *. rewrite wleb_zero in * by lia.
assert (H2' : rdn ASEGS0 M (Z_to_bv 64 a + nat_to_word w1)%bv w2 = Some (repeat (Z_to_bv 8 0) w2)).
{ replace (Z_to_bv 64 a + nat_to_word w1)%bv with (Z_to_bv 64 (a + Z.of_nat w1)); [exact H2|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small (Z.of_nat w1)) by lia. reflexivity. }
rewrite (rdn_app ASEGS0 M w1 w2 (Z_to_bv 64 a) _ _ H1 H2'). rewrite repeat_app. reflexivity.
Qed.
