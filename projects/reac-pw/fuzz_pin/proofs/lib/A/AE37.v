(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE37.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: by h-small-a8, x2 (asan.module_dtor -> __asan_unregister_globals) ported to libreac/fuzz_scene's five registered globals, measured on the pinned image: x2_rodata's asan_globals entries are scene's five descriptors (beg, size, size_with_redzone, module_name, has_dynamic_init, location, odr_indicator), x2_shw is the shadow of each global plus the 40-byte shadow of the descriptor array (as XW2), each written shadow byte is shown present either as a 1-byte const cell or inside a Tfib_zero_shadow range (win_chk / zrun_present), and the 1-byte ODR indicator 0x5d5e80 that UnregisterGlobal clears is a writable region. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AE37.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AB1v AE34 AF0l AF0m AE3g AE2p AE3i AE3h AE3m AE23 AF0x AE20 AE2y AE7f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation tbl2 := tbl_x213 (only parsing).
Notation tbl2_ok := tbl_x213_ok (only parsing).
Definition x2_rodata : list (Z * Z * list (Z * N * Z)) :=
[ (0x103a0, 8, [(0, 8%N, 0xafffff00000fffff)]);
(0x99030, 72, [(0, 8%N, 0x1310a0); (8, 8%N, 0x9af00); (16, 8%N, 0x133128); (24, 8%N, 0x9edf8); (32, 8%N, 0xa15f8);
(40, 8%N, 0xa22e8); (48, 8%N, 0xa22f0); (56, 8%N, 0xa22e0); (64, 8%N, 0x9aec8)]);
(0x99cc8, 16, [(0, 8%N, 0x9d910); (8, 8%N, 0x9df10)]);
(0x9aec8, 8, [(0, 8%N, 0x91618)]);
(0x9d910, 1536, [(0, 8%N, 0x20d80); (8, 8%N, 0x2); (16, 8%N, 0x20); (32, 8%N, 0x20da0); (40, 8%N, 0x0); (48, 8%N, 0x0); (56, 8%N, 0xffffffffffffffff);
(64, 8%N, 0x20dc0); (72, 8%N, 0x6); (80, 8%N, 0x20); (96, 8%N, 0x211e0); (104, 8%N, 0x0); (112, 8%N, 0x0); (120, 8%N, 0xffffffffffffffff);
(128, 8%N, 0x20de0); (136, 8%N, 0x17); (144, 8%N, 0x40); (160, 8%N, 0x211e0); (168, 8%N, 0x0); (176, 8%N, 0x0); (184, 8%N, 0xffffffffffffffff);
(192, 8%N, 0x20e20); (200, 8%N, 0x6); (208, 8%N, 0x20); (224, 8%N, 0x211e0); (232, 8%N, 0x0); (240, 8%N, 0x0); (248, 8%N, 0xffffffffffffffff);
(256, 8%N, 0x20e40); (264, 8%N, 0x16); (272, 8%N, 0x40); (288, 8%N, 0x211e0); (296, 8%N, 0x0); (304, 8%N, 0x0); (312, 8%N, 0xffffffffffffffff);
(320, 8%N, 0x20e80); (328, 8%N, 0x7); (336, 8%N, 0x20); (352, 8%N, 0x211e0); (360, 8%N, 0x0); (368, 8%N, 0x0); (376, 8%N, 0xffffffffffffffff);
(384, 8%N, 0x20ea0); (392, 8%N, 0x1d); (400, 8%N, 0x40); (416, 8%N, 0x211e0); (424, 8%N, 0x0); (432, 8%N, 0x0); (440, 8%N, 0xffffffffffffffff);
(448, 8%N, 0x20ee0); (456, 8%N, 0xc); (464, 8%N, 0x20); (480, 8%N, 0x211e0); (488, 8%N, 0x0); (496, 8%N, 0x0); (504, 8%N, 0xffffffffffffffff);
(512, 8%N, 0x20f00); (520, 8%N, 0x1d); (528, 8%N, 0x40); (544, 8%N, 0x211e0); (552, 8%N, 0x0); (560, 8%N, 0x0); (568, 8%N, 0xffffffffffffffff);
(576, 8%N, 0x20f40); (584, 8%N, 0x6); (592, 8%N, 0x20); (608, 8%N, 0x211e0); (616, 8%N, 0x0); (624, 8%N, 0x0); (632, 8%N, 0xffffffffffffffff);
(640, 8%N, 0x20f60); (648, 8%N, 0x17); (656, 8%N, 0x40); (672, 8%N, 0x211e0); (680, 8%N, 0x0); (688, 8%N, 0x0); (696, 8%N, 0xffffffffffffffff);
(704, 8%N, 0x20fa0); (712, 8%N, 0x6); (720, 8%N, 0x20); (736, 8%N, 0x211e0); (744, 8%N, 0x0); (752, 8%N, 0x0); (760, 8%N, 0xffffffffffffffff);
(768, 8%N, 0x20fc0); (776, 8%N, 0x18); (784, 8%N, 0x40); (800, 8%N, 0x211e0); (808, 8%N, 0x0); (816, 8%N, 0x0); (824, 8%N, 0xffffffffffffffff);
(832, 8%N, 0x21000); (840, 8%N, 0x7); (848, 8%N, 0x20); (864, 8%N, 0x211e0); (872, 8%N, 0x0); (880, 8%N, 0x0); (888, 8%N, 0xffffffffffffffff);
(896, 8%N, 0x21020); (904, 8%N, 0x18); (912, 8%N, 0x40); (928, 8%N, 0x211e0); (936, 8%N, 0x0); (944, 8%N, 0x0); (952, 8%N, 0xffffffffffffffff);
(960, 8%N, 0x21060); (968, 8%N, 0x7); (976, 8%N, 0x20); (992, 8%N, 0x211e0); (1000, 8%N, 0x0); (1008, 8%N, 0x0); (1016, 8%N, 0xffffffffffffffff);
(1024, 8%N, 0x21080); (1032, 8%N, 0x18); (1040, 8%N, 0x40); (1056, 8%N, 0x211e0); (1064, 8%N, 0x0); (1072, 8%N, 0x0); (1080, 8%N, 0xffffffffffffffff);
(1088, 8%N, 0x210c0); (1096, 8%N, 0x7); (1104, 8%N, 0x20); (1120, 8%N, 0x211e0); (1128, 8%N, 0x0); (1136, 8%N, 0x0); (1144, 8%N, 0xffffffffffffffff);
(1152, 8%N, 0x210e0); (1160, 8%N, 0x17); (1168, 8%N, 0x40); (1184, 8%N, 0x211e0); (1192, 8%N, 0x0); (1200, 8%N, 0x0); (1208, 8%N, 0xffffffffffffffff);
(1216, 8%N, 0x21120); (1224, 8%N, 0x7); (1232, 8%N, 0x20); (1248, 8%N, 0x211e0); (1256, 8%N, 0x0); (1264, 8%N, 0x0); (1272, 8%N, 0xffffffffffffffff);
(1280, 8%N, 0x21140); (1288, 8%N, 0x17); (1296, 8%N, 0x40); (1312, 8%N, 0x211e0); (1320, 8%N, 0x0); (1328, 8%N, 0x0); (1336, 8%N, 0xffffffffffffffff);
(1344, 8%N, 0x21180); (1352, 8%N, 0x7); (1360, 8%N, 0x20); (1376, 8%N, 0x211e0); (1384, 8%N, 0x0); (1392, 8%N, 0x0); (1400, 8%N, 0xffffffffffffffff);
(1408, 8%N, 0x211a0); (1416, 8%N, 0x18); (1424, 8%N, 0x40); (1440, 8%N, 0x211e0); (1448, 8%N, 0x0); (1456, 8%N, 0x0); (1464, 8%N, 0xffffffffffffffff);
(1472, 8%N, 0x97ee0); (1480, 8%N, 0xcb8); (1488, 8%N, 0xfe0); (1504, 8%N, 0x211e0); (1512, 8%N, 0x0); (1520, 8%N, 0x0); (1528, 8%N, 0x5d3c80)]);
(0x9ee10, 8, [(0, 8%N, 0x101010000000001)]);
(0x9ee40, 8, [(0, 8%N, 0x1000100000000)]);
(0xa0e5c, 1, [(0, 1%N, 1)]);
(0xa15f8, 8, [(0, 8%N, 0x7fff8000)]);
(0xa22d8, 1, [(0, 1%N, 1)]);
(0xa22e0, 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
(0x1310a0, 8, [(0, 8%N, 0x1000)]);
(0x1331a0, 8, [(0, 8%N, 0xffffffffffffffff)]) ].
Definition ro_chunk (base : Z) (c : Z * N * Z) : YP09.chunk := YP09.mkChunk (base + fst (fst c)) (CVal (snd (fst c)) (SLit (snd c))).
Definition ro_region (r : Z * Z * list (Z * N * Z)) : YP09.region :=
YP09.mkRegion None (fst (fst r)) (fst (fst r) + snd (fst r)) (fst (fst r)) (fst (fst r)) (map (ro_chunk (fst (fst r))) (snd r)).
Definition X2_STK : Z := 272.
(* the ODR indicator byte of __odr_asan_gen_reac_scene_placeholder (asan), which __asan_unregister_globals clears (sb zero, 0(odr_indicator)) *)
Definition X2_ODR : Z := 0x5d3c80.
Definition x2_shw : list (Z * Z) := [(0x7fffc1b0, 4); (0x7fffc1b8, 4); (0x7fffc1bc, 8); (0x7fffc1c4, 4); (0x7fffc1c8, 8); (0x7fffc1d0, 4); (0x7fffc1d4, 8); (0x7fffc1dc, 4); (0x7fffc1e0, 8); (0x7fffc1e8, 4); (0x7fffc1ec, 8); (0x7fffc1f4, 4); (0x7fffc1f8, 8); (0x7fffc200, 4); (0x7fffc204, 8); (0x7fffc20c, 4); (0x7fffc210, 8); (0x7fffc218, 4); (0x7fffc21c, 8); (0x7fffc224, 4); (0x7fffc228, 8); (0x7fffc230, 4); (0x7fffc234, 8); (0x8000afdc, 508); (0x8000bb22, 192)].
Definition shw_region (w : Z * Z) : YP09.region :=
YP09.mkRegion None (fst w) (fst w + snd w) (fst w) (fst w + snd w) [].
Definition x2_regions : smem :=
YP09.mkRegion (Some 2%nat) (- X2_STK) 0 (- X2_STK) 0 []
:: cellr 0x9df40 8 (SLit 1) true
:: cellr 0x9eeb0 8 (SLit 0) true
:: shw_region (X2_ODR, 1)
:: map shw_region x2_shw ++ map ro_region x2_rodata.
Definition ss_x2 : sstate := mkSS X2_PC sr_atoms x2_regions None (mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4)] [] []).
Definition x2_st : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl2 FUEL ss_x2).
Lemma x2_run : sym_runN tfibsegs tbl2 FUEL ss_x2 = (x2_st, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma x2_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl2 FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl2 tbl2_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition const_chk (ly : alayout) (a : Z) (n : N) (v : Z) : bool :=
match cell_lookup (Tfib_const ly) (ANum a) with
| Some (ACell (ANum a') w' (AV (ANum v'))) => (a' =? a) && Nat.eqb w' (N.to_nat n) && (v' =? v)
| _ => false
end.
Lemma const_chk_sound : forall ly a n v, const_chk ly a n v = true ->
cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) (N.to_nat n) (AV (ANum v))).
Proof.
intros ly a n v H. unfold const_chk in H.
destruct (cell_lookup (Tfib_const ly) (ANum a)) as [[e w av]|]; [|discriminate].
destruct e; try discriminate. destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Definition rodata_chk (ly : alayout) : bool :=
forallb (fun r => (0 <=? fst (fst r)) && (fst (fst r) + snd (fst r) <=? 2 ^ 47) &&
forallb (fun c => const_chk ly (fst (fst r) + fst (fst c)) (snd (fst c)) (snd c)
&& (0 <=? snd c) && (snd c <? 2 ^ (8 * Z.of_N (snd (fst c)))) && (Z.of_N (snd (fst c)) <=? 8)) (snd r))
x2_rodata.
Lemma rodata_chk_true : forall ly, rodata_chk ly = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Fixpoint zrange (lo : Z) (n : nat) : list Z := match n with O => [] | S k => lo :: zrange (lo + 1) k end.
Lemma In_zrange : forall n lo a, lo <= a < lo + Z.of_nat n -> In a (zrange lo n).
Proof.
induction n as [|n IH]; intros lo a Ha; [lia|]. cbn [zrange].
destruct (Z.eq_dec a lo) as [->|Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.
Definition x2_shw_const : list (Z * Z) := [(0x7fffc1b0, 4); (0x7fffc1b8, 4); (0x7fffc1be, 10); (0x7fffc1ca, 10); (0x7fffc1d7, 5); (0x7fffc1dd, 3); (0x7fffc1e3, 9); (0x7fffc1ee, 10); (0x7fffc1fb, 9); (0x7fffc207, 9); (0x7fffc213, 9); (0x7fffc21e, 10); (0x7fffc22a, 10); (0x7fffc237, 5); (0x8000b173, 101); (0x8000bb22, 192)].
Definition x2_shbytes : list Z := flat_map (fun w => zrange (fst w) (Z.to_nat (snd w))) x2_shw_const.
Definition shbyte_chk (ly : alayout) : bool :=
forallb (fun a => match cell_lookup (Tfib_const ly) (ANum a) with
| Some (ACell (ANum a') 1%nat (AV (ANum v))) => (a' =? a) && (0 <=? v) && (v <? 256)
| _ => false end) x2_shbytes.
Lemma shbyte_chk_true : forall ly, shbyte_chk ly = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Section S.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis MU0 : forall ly, cell_lookup (Tfib_const ly) (ANum 0x9eeb0) = Some (ACell (ANum 0x9eeb0) 8 (AV (ANum 0))).
Lemma rodata_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region x2_rodata).
Proof.
intros ly S H mem E HM. pose proof (rodata_chk_true ly) as Hc. unfold rodata_chk in Hc.
rewrite forallb_forall in Hc. apply Forall_map. apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hc _ Hin). cbn [fst snd] in Hc. apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [H0 Hhi].
apply Z.leb_le in H0. apply Z.leb_le in Hhi.
unfold ro_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
rewrite forallb_forall in Hcs. apply Forall_map. apply Forall_forall. intros [[off n] v] Hc'.
specialize (Hcs _ Hc'). cbn [fst snd] in Hcs.
apply andb_prop in Hcs as [Hcs H4]. apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
unfold ro_chunk. cbn [fst snd].
eapply (chunk_ok_val tfibsegs E _ 0 (base + off) n (SLit v) v); [reflexivity | lia | lia |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S H mem (base + off) (N.to_nat n) v HM (const_chk_sound _ _ _ _ H1)).
Qed.
Lemma shbytes_present : forall ly S (H : word -> bool) mem a,
ARm B ly S (aview tfibsegs H mem) -> In a x2_shbytes -> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b.
Proof.
intros ly S H mem a HM Hin. pose proof (shbyte_chk_true ly) as Hc. unfold shbyte_chk in Hc.
rewrite forallb_forall in Hc. specialize (Hc a Hin). cbn beta in Hc.
destruct (cell_lookup (Tfib_const ly) (ANum a)) as [[e w av]|] eqn:HL; [|discriminate].
destruct e; try discriminate. destruct w as [|[|w]]; try discriminate.
destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply Z.eqb_eq in Hc. subst.
pose proof (tfib_const_lookup B TB ly S H mem a 1 _ HM HL) as Hv.
specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. eexists. exact Hv.
Qed.
Definition x2_zrun : list (Z * Z * Z * Z) := [(0x20de0, 0x20df0 - 0x20de0, 0, 2); (0x20e40, 0x20e50 - 0x20e40, 0, 2); (0x20ea0, 0x20eb8 - 0x20ea0, 0, 3); (0x20ee0, 0x20ee8 - 0x20ee0, 0, 1); (0x20f00, 0x20f18 - 0x20f00, 0, 3); (0x20f60, 0x20f70 - 0x20f60, 0, 2); (0x20fc0, 0x20fd8 - 0x20fc0, 0, 3); (0x21020, 0x21038 - 0x21020, 0, 3); (0x21080, 0x21098 - 0x21080, 0, 3); (0x210e0, 0x210f0 - 0x210e0, 0, 2); (0x21140, 0x21150 - 0x21140, 0, 2); (0x211a0, 0x211b8 - 0x211a0, 0, 3); (0x211e0, 0x98b98 - 0x211e0, 60832, 407)].
Definition zrun_ok : bool :=
forallb (fun z => existsb (fun r => (fst r =? fst (fst (fst z))) && (snd r =? snd (fst (fst z)))) Tfib_zero_shadow
&& (0 <=? snd (fst z)) && (snd (fst z) + snd z <=? snd (fst (fst z)) / 8)) x2_zrun.
Lemma zrun_ok_true : zrun_ok = true.
Proof. vm_compute. reflexivity. Qed.
Definition in_zrun (o : Z) : bool :=
existsb (fun z => (shadow_of_addr SHADOW_OFF (fst (fst (fst z))) + snd (fst z) <=? o) &&
(o <? shadow_of_addr SHADOW_OFF (fst (fst (fst z))) + snd (fst z) + snd z)) x2_zrun.
Definition win_chk : bool :=
forallb (fun w => (0 <=? snd w) && forallb (fun o => in_zrun o || existsb (Z.eqb o) x2_shbytes) (zrange (fst w) (Z.to_nat (snd w)))) x2_shw.
Lemma win_chk_true : win_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma zrun_present : forall ly S (H : word -> bool) mem o,
ARm B ly S (aview tfibsegs H mem) -> in_zrun o = true -> exists b, mbyte tfibsegs (mrestrict H mem) o = Some b.
Proof.
intros ly S H mem o HM Ho. unfold in_zrun in Ho. apply existsb_exists in Ho as ([[[lo len] k0] n] & Hz & Ho). cbn [fst snd] in Ho.
apply andb_prop in Ho as [Ho1 Ho2]. apply Z.leb_le in Ho1. apply Z.ltb_lt in Ho2.
pose proof zrun_ok_true as Hc. unfold zrun_ok in Hc. rewrite forallb_forall in Hc. specialize (Hc _ Hz). cbn [fst snd] in Hc.
apply andb_prop in Hc as [Hc Hn]. apply andb_prop in Hc as [Hr Hk]. apply Z.leb_le in Hn. apply Z.leb_le in Hk.
apply existsb_exists in Hr as ([rlo rlen] & Hin & Hr). cbn [fst snd] in Hr.
apply andb_prop in Hr as [Hr1 Hr2]. apply Z.eqb_eq in Hr1. apply Z.eqb_eq in Hr2. subst rlo rlen.
pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly S _ HM) (lo, len)
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh _ TB); exact Hin)) as HZ.
specialize (HZ (o - shadow_of_addr SHADOW_OFF lo) ltac:(cbn [fst snd]; lia)). cbn [fst snd] in HZ.
replace (shadow_of_addr SHADOW_OFF lo + (o - shadow_of_addr SHADOW_OFF lo)) with o in HZ by lia.
unfold aview in HZ. destruct (mbyte tfibsegs (mrestrict H mem) o) as [b|]; [exists b; reflexivity | discriminate].
Qed.
Lemma win_byte : forall w o, In w x2_shw -> fst w <= o < fst w + snd w -> in_zrun o = true \/ In o x2_shbytes.
Proof.
intros w o Hw Ho. pose proof win_chk_true as Hc. unfold win_chk in Hc. rewrite forallb_forall in Hc. specialize (Hc w Hw).
apply andb_prop in Hc as [Hn Hc]. apply Z.leb_le in Hn. rewrite forallb_forall in Hc.
specialize (Hc o (In_zrange (Z.to_nat (snd w)) (fst w) o ltac:(rewrite Z2Nat.id by lia; lia))). apply orb_true_iff in Hc as [Hc|Hc]; [left; exact Hc|right].
apply existsb_exists in Hc as (o' & Hin & He). apply Z.eqb_eq in He. subst o'. exact Hin.
Qed.
Lemma shw_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map shw_region x2_shw).
Proof.
intros ly S H mem E HM. apply Forall_map. apply Forall_forall. intros [lo n] Hin.
assert (Hr : (lo = 0x7fffc1b0 /\ n = 4) \/ (lo = 0x7fffc1b8 /\ n = 4) \/ (lo = 0x7fffc1bc /\ n = 8) \/ (lo = 0x7fffc1c4 /\ n = 4) \/ (lo = 0x7fffc1c8 /\ n = 8) \/ (lo = 0x7fffc1d0 /\ n = 4) \/ (lo = 0x7fffc1d4 /\ n = 8) \/ (lo = 0x7fffc1dc /\ n = 4) \/ (lo = 0x7fffc1e0 /\ n = 8) \/ (lo = 0x7fffc1e8 /\ n = 4) \/ (lo = 0x7fffc1ec /\ n = 8) \/ (lo = 0x7fffc1f4 /\ n = 4) \/ (lo = 0x7fffc1f8 /\ n = 8) \/ (lo = 0x7fffc200 /\ n = 4) \/ (lo = 0x7fffc204 /\ n = 8) \/ (lo = 0x7fffc20c /\ n = 4) \/ (lo = 0x7fffc210 /\ n = 8) \/ (lo = 0x7fffc218 /\ n = 4) \/ (lo = 0x7fffc21c /\ n = 8) \/ (lo = 0x7fffc224 /\ n = 4) \/ (lo = 0x7fffc228 /\ n = 8) \/ (lo = 0x7fffc230 /\ n = 4) \/ (lo = 0x7fffc234 /\ n = 8) \/ (lo = 0x8000afdc /\ n = 508) \/ (lo = 0x8000bb22 /\ n = 192)).
{ cbn in Hin. destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]]]]]]]]]]]]]]]]]]]]]; injection Hq as <- <-; tauto. }
unfold shw_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. rewrite Z.add_0_l.
assert (Hb2 : exists b, mbyte tfibsegs (mrestrict H mem) o = Some b).
{ destruct (win_byte (lo, n) o Hin ltac:(cbn [fst snd]; lia)) as [Hz|Hs];
[exact (zrun_present ly S H mem o HM Hz) | exact (shbytes_present ly S H mem o HM Hs)]. }
destruct Hb2 as [b Hb].
apply (mbyte_high_writable _ o b); [unfold TFIB_IMG_END; lia | exact Hb].
Qed.
Lemma zi8_14ea00 : wseg_ok tfibsegs (Z_to_bv 64 0x9df40) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma zi8_14f970 : wseg_ok tfibsegs (Z_to_bv 64 0x9eeb0) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma zi1_odr : wseg_ok tfibsegs (Z_to_bv 64 X2_ODR) (Z.to_nat 1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma x2_windows : forall E a, in_wrange E (ss_mem ss_x2) a ->
(bv_unsigned (ew E 2) - X2_STK <= a < bv_unsigned (ew E 2)) \/ XW2 a.
Proof.
intros E a Hin. destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
cbn in Ht. unfold XW2. unfold X2_STK, X2_ODR in *.
repeat (destruct Ht as [Hq|Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hr; lia|]). destruct Ht.
Qed.
Theorem x2_realizes : xret_realizes_noar tfibsegs B X2_PC XW2 XTRUE.
Proof.
intros ly S W regs mem md HPRE _. pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HES : ESTACK = 4096) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (proj1 HAR) as HM.
unfold cfg_at. change (w64 X2_PC) with (Z_to_bv 64 X2_PC).
set (sp0 := spZ regs) in *.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (E := Ereg regs (@nil word)).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (HS0 : st_ok tfibsegs E ss_x2 (restrict (w_H W) (mkst regs (Z_to_bv 64 X2_PC) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_x2. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold x2_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split; [exact (shw_ok ly S _ mem E HM) | exact (rodata_ok ly S _ mem E HM)]]]]].
+ apply (region_ok_stack tfibsegs E _ 2 sp0 (- X2_STK)); [exact E2 | unfold X2_STK; lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. unfold X2_STK in Ha. lia.
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0x9df40 8); [exact zi8_14ea00 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 1); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S _ mem 0x9df40 8 1 HM ltac:(vm_compute; reflexivity)).
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0x9eeb0 8); [exact zi8_14f970 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 0); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S _ mem 0x9eeb0 8 0 HM (MU0 ly)).
+ unfold region_ok, shw_region. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold X2_ODR; lia|]. split; [unfold X2_ODR; lia|]. split; [|constructor].
intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ X2_ODR 1); [exact zi1_odr | unfold X2_ODR in *; lia | unfold X2_ODR in *; lia | unfold X2_ODR in *; lia | unfold X2_ODR in *; lia].
- apply pairwise_disjoint_of_extents. unfold x2_regions, x2_shw, x2_rodata, cellr, shw_region, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2. unfold X2_STK, X2_ODR.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
change (2 ^ 4) with 16. repeat split; lia. }
eapply SRr_bind; [apply (x2_phase W E ss_x2 x2_st _ _ md HS0 x2_run)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
eapply (SRr_ret_at tfibsegs tbl2 tbl2_ok Hwx W E); [exact HS1 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ : forall x : word, ~ ((sp0 - X2_STK <= bv_unsigned x < sp0) \/ XW2 (bv_unsigned x)) -> ms_mem ms1 x = mem x).
{ intros x Hx. apply HF1. intros Hin. apply Hx. destruct (x2_windows E _ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [left; exact Hw | right; exact Hw]. }
assert (MEQr : forall x : word, ~ ((sp0 - X2_STK <= bv_unsigned x < sp0) \/ XW2 (bv_unsigned x)) ->
mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x).
{ intros x Hx. apply HFr1. intros Hin. apply Hx. destruct (x2_windows E _ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [left; exact Hw | right; exact Hw]. }
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - X2_STK <= a < sp0) -> ~ XW2 a ->
aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a).
{ intros a Hr H1 H2. apply aview_eq_of. apply MEQr. rewrite unsigned_lit_small by lia. tauto. }
assert (PRS : forall a, sp0 - X2_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. unfold X2_STK in Ha. apply (apresent_of_writable (w_H W) (ms_mem ms1) a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS1 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
pose proof (Forall_inv Hrs) as Hr0. destruct Hr0 as (_ & _ & Hw & _).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite E2 in Hw. unfold X2_STK in Hw.
replace a with (sp0 + (a - sp0)) by lia. apply Hw. lia. }
rreg HS1 (1%bv : bv 5) Q1. replace (ew E 1) with (getr regs 1) in Q1 by (symmetry; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
replace (v_jalr (getr (ms_regs ms1) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
split; [reflexivity|]. exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
split; [reflexivity|].
split; [|split; [|split]].
- exact (aregs_preserved_of_st_ok _ E _ _ regs [] HS1 ltac:(split; [intros i Hi; reflexivity | reflexivity]) ltac:(vm_compute; reflexivity)).
- apply with_vm_backing_same.
- intros a Hr Hs Hx. apply AV; [exact Hr | unfold X2_STK; unfold sp0 in *; lia | exact Hx].
- intros a Hr Hx Hp.
destruct (Z_lt_le_dec a (sp0 - X2_STK)) as [L1|L1]; [| destruct (Z_lt_le_dec a sp0) as [L2|L2]; [apply PRS; lia|]].
all: destruct Hp as [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite MEQ; [exact Hb|]; rewrite unsigned_lit_small by lia; intros [Hw|Hw]; [lia | exact (Hx Hw)].
Qed.
End S.
End d.
