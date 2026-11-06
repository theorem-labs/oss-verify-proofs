(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE37.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (34 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: asan.module_dtor's data are fuzz_reply.asan's: x2_rodata's descriptor row is the image's 27 asan_globals descriptors (0xa2320..0xa29e0, the words the walk reads), x2_shw the four shadow runs __asan_unregister_globals clears (the 27 globals' size_with_redzone / 8 and the descriptor array's 1728 / 8), and each shadow byte is present either as a start-up const cell (Tfib_const_shadow) or inside a Tfib_zero_shadow range (zs_present), replacing cgif's per-byte list and its single zero byte. *)
(* Provenance of those data (HAND-WRITTEN, not generated): the 27 x 64-byte descriptor words were read from the image file
   fuzz_reply.asan (sha256 42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a) at 0xa2320..0xa29e0 by an
   ad-hoc ELF reader (PT_LOAD mapping, little-endian 8-byte words); x2_shw is 0x7fff8000 + addr / 8 over each global's
   [beg, beg + size_with_redzone) and over the descriptor array, merged where adjacent. No committed generator emits them.
   The kernel checks them against the GENERATED start-up tables: rodata_chk_true requires every stated word to be a cell of
   AF0m.v's Tfib_const (af0m.py output), shbyte_chk_true requires every shadow byte of x2_shw to be an AF0m.v
   Tfib_const_shadow cell or inside AF0m.v's Tfib_zero_shadow, and x2_run requires the walk to read and write only these
   regions. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AE34 AF0l AF0m AE3g AE2p AE3i AE3h AE3m AE23 AF0x AE20 AE2y AE7f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
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
(0x9d9b0, 72, [(0, 8%N, 0x135b60); (8, 8%N, 0x9f8a8); (16, 8%N, 0x137be8); (24, 8%N, 0xa38b8); (32, 8%N, 0xa60b8);
(40, 8%N, 0xa6da8); (48, 8%N, 0xa6db0); (56, 8%N, 0xa6da0); (64, 8%N, 0x9f870)]);
(0x9e648, 16, [(0, 8%N, 0xa2320); (8, 8%N, 0xa29e0)]);
(0x9f870, 8, [(0, 8%N, 0x96900)]);
(0xa2320, 1728, [(0, 8%N, 0x20e80); (8, 8%N, 0x32); (16, 8%N, 0x60); (32, 8%N, 0x20fa0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0xffffffffffffffff);
(64, 8%N, 0x20ee0); (72, 8%N, 0x1); (80, 8%N, 0x20); (96, 8%N, 0x20fa0); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 0xffffffffffffffff);
(128, 8%N, 0x20f00); (136, 8%N, 0x5); (144, 8%N, 0x20); (160, 8%N, 0x20fa0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0xffffffffffffffff);
(192, 8%N, 0x20f20); (200, 8%N, 0xe); (208, 8%N, 0x20); (224, 8%N, 0x20fa0); (232, 8%N, 0); (240, 8%N, 0); (248, 8%N, 0xffffffffffffffff);
(256, 8%N, 0x20f40); (264, 8%N, 0x6); (272, 8%N, 0x20); (288, 8%N, 0x20fa0); (296, 8%N, 0); (304, 8%N, 0); (312, 8%N, 0xffffffffffffffff);
(320, 8%N, 0x20f60); (328, 8%N, 0x4); (336, 8%N, 0x20); (352, 8%N, 0x20fa0); (360, 8%N, 0); (368, 8%N, 0); (376, 8%N, 0xffffffffffffffff);
(384, 8%N, 0x20f80); (392, 8%N, 0x7); (400, 8%N, 0x20); (416, 8%N, 0x20fa0); (424, 8%N, 0); (432, 8%N, 0); (440, 8%N, 0xffffffffffffffff);
(448, 8%N, 0xa1fa0); (456, 8%N, 0x8); (464, 8%N, 0x20); (480, 8%N, 0x20fa0); (488, 8%N, 0); (496, 8%N, 0); (504, 8%N, 0xffffffffffffffff);
(512, 8%N, 0xa1fc0); (520, 8%N, 0x4); (528, 8%N, 0x20); (544, 8%N, 0x20fa0); (552, 8%N, 0); (560, 8%N, 0); (568, 8%N, 0xffffffffffffffff);
(576, 8%N, 0xa1fe0); (584, 8%N, 0x4); (592, 8%N, 0x20); (608, 8%N, 0x20fa0); (616, 8%N, 0); (624, 8%N, 0); (632, 8%N, 0xffffffffffffffff);
(640, 8%N, 0x5d8740); (648, 8%N, 0x8); (656, 8%N, 0x20); (672, 8%N, 0x20fa0); (680, 8%N, 0); (688, 8%N, 0); (696, 8%N, 0xffffffffffffffff);
(704, 8%N, 0x5d8760); (712, 8%N, 0x1); (720, 8%N, 0x20); (736, 8%N, 0x20fa0); (744, 8%N, 0); (752, 8%N, 0); (760, 8%N, 0xffffffffffffffff);
(768, 8%N, 0x5d8780); (776, 8%N, 0x4); (784, 8%N, 0x20); (800, 8%N, 0x20fa0); (808, 8%N, 0); (816, 8%N, 0); (824, 8%N, 0xffffffffffffffff);
(832, 8%N, 0x5d87a0); (840, 8%N, 0x4); (848, 8%N, 0x20); (864, 8%N, 0x20fa0); (872, 8%N, 0); (880, 8%N, 0); (888, 8%N, 0xffffffffffffffff);
(896, 8%N, 0x5d87c0); (904, 8%N, 0x8); (912, 8%N, 0x20); (928, 8%N, 0x20fa0); (936, 8%N, 0); (944, 8%N, 0); (952, 8%N, 0xffffffffffffffff);
(960, 8%N, 0x5d87e0); (968, 8%N, 0x1); (976, 8%N, 0x20); (992, 8%N, 0x20fa0); (1000, 8%N, 0); (1008, 8%N, 0); (1016, 8%N, 0xffffffffffffffff);
(1024, 8%N, 0x5d8800); (1032, 8%N, 0x4); (1040, 8%N, 0x20); (1056, 8%N, 0x20fa0); (1064, 8%N, 0); (1072, 8%N, 0); (1080, 8%N, 0xffffffffffffffff);
(1088, 8%N, 0x5d8820); (1096, 8%N, 0x4); (1104, 8%N, 0x20); (1120, 8%N, 0x20fa0); (1128, 8%N, 0); (1136, 8%N, 0); (1144, 8%N, 0xffffffffffffffff);
(1152, 8%N, 0x5d8840); (1160, 8%N, 0x8); (1168, 8%N, 0x20); (1184, 8%N, 0x20fa0); (1192, 8%N, 0); (1200, 8%N, 0); (1208, 8%N, 0xffffffffffffffff);
(1216, 8%N, 0x5d8860); (1224, 8%N, 0x1); (1232, 8%N, 0x20); (1248, 8%N, 0x20fa0); (1256, 8%N, 0); (1264, 8%N, 0); (1272, 8%N, 0xffffffffffffffff);
(1280, 8%N, 0x5d8880); (1288, 8%N, 0x1); (1296, 8%N, 0x20); (1312, 8%N, 0x20fa0); (1320, 8%N, 0); (1328, 8%N, 0); (1336, 8%N, 0xffffffffffffffff);
(1344, 8%N, 0x5d88a0); (1352, 8%N, 0x1); (1360, 8%N, 0x20); (1376, 8%N, 0x20fa0); (1384, 8%N, 0); (1392, 8%N, 0); (1400, 8%N, 0xffffffffffffffff);
(1408, 8%N, 0x5d88c0); (1416, 8%N, 0x8); (1424, 8%N, 0x20); (1440, 8%N, 0x20fa0); (1448, 8%N, 0); (1456, 8%N, 0); (1464, 8%N, 0xffffffffffffffff);
(1472, 8%N, 0x5d88e0); (1480, 8%N, 0x180); (1488, 8%N, 0x1e0); (1504, 8%N, 0x20fa0); (1512, 8%N, 0); (1520, 8%N, 0); (1528, 8%N, 0xffffffffffffffff);
(1536, 8%N, 0x5d8ac0); (1544, 8%N, 0x28); (1552, 8%N, 0x60); (1568, 8%N, 0x20fa0); (1576, 8%N, 0); (1584, 8%N, 0); (1592, 8%N, 0xffffffffffffffff);
(1600, 8%N, 0x5d8b20); (1608, 8%N, 0x8); (1616, 8%N, 0x20); (1632, 8%N, 0x20fa0); (1640, 8%N, 0); (1648, 8%N, 0); (1656, 8%N, 0xffffffffffffffff);
(1664, 8%N, 0x5d8b40); (1672, 8%N, 0x8); (1680, 8%N, 0x20); (1696, 8%N, 0x20fa0); (1704, 8%N, 0); (1712, 8%N, 0); (1720, 8%N, 0xffffffffffffffff)]);
(0xa38d0, 8, [(0, 8%N, 0x101010000000001)]);
(0xa3900, 8, [(0, 8%N, 0x1000100000000)]);
(0xa591c, 1, [(0, 1%N, 1)]);
(0xa60b8, 8, [(0, 8%N, 0x7fff8000)]);
(0xa6d98, 1, [(0, 1%N, 1)]);
(0xa6da0, 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
(0x135b60, 8, [(0, 8%N, 0x1000)]);
(0x137c60, 8, [(0, 8%N, 0xffffffffffffffff)]) ].
Definition ro_chunk (base : Z) (c : Z * N * Z) : YP09.chunk := YP09.mkChunk (base + fst (fst c)) (CVal (snd (fst c)) (SLit (snd c))).
Definition ro_region (r : Z * Z * list (Z * N * Z)) : YP09.region :=
YP09.mkRegion None (fst (fst r)) (fst (fst r) + snd (fst r)) (fst (fst r)) (fst (fst r)) (map (ro_chunk (fst (fst r))) (snd r)).
Definition X2_STK : Z := 272.
Definition x2_shw : list (Z * Z) := [(0x7fffc1d0, 36); (0x8000c3f4, 12); (0x8000c464, 216); (0x800b30e8, 132)].
Definition shw_region (w : Z * Z) : YP09.region :=
YP09.mkRegion None (fst w) (fst w + snd w) (fst w) (fst w + snd w) [].
Definition x2_regions : smem :=
YP09.mkRegion (Some 2%nat) (- X2_STK) 0 (- X2_STK) 0 []
:: cellr 0xa2a00 8 (SLit 1) true
:: cellr 0xa3970 8 (SLit 0) true
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
Definition x2_shbytes : list Z := flat_map (fun w => zrange (fst w) (Z.to_nat (snd w))) x2_shw.
Definition cell1_ok (ly : alayout) (a : Z) : bool :=
match cell_lookup (Tfib_const ly) (ANum a) with
| Some (ACell (ANum a') 1%nat (AV (ANum v))) => (a' =? a) && (0 <=? v) && (v <? 256)
| _ => false end.
Definition zs_cov (a : Z) : bool :=
existsb (fun r : Z * Z => (shadow_of_addr SHADOW_OFF (fst r) <=? a) && (a <? shadow_of_addr SHADOW_OFF (fst r) + snd r / 8)) Tfib_zero_shadow.
Definition shbyte_chk (ly : alayout) : bool := forallb (fun a => cell1_ok ly a || zs_cov a) x2_shbytes.
Lemma shbyte_chk_true : forall ly, shbyte_chk ly = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Section S.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis WL : icpt_laws_x B ARx.
Hypothesis TB : TfibSyms B.
Hypothesis MU0 : forall ly, cell_lookup (Tfib_const ly) (ANum 0xa3970) = Some (ACell (ANum 0xa3970) 8 (AV (ANum 0))).
Lemma rodata_ok : forall ly (H : word -> bool) mem E,
Forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region x2_rodata).
Proof.
intros ly H mem E HM. pose proof (rodata_chk_true ly) as Hc. unfold rodata_chk in Hc.
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
rewrite Z.add_0_l. exact (tfib_const_lookup_x B TB ly H mem (base + off) (N.to_nat n) v HM (const_chk_sound _ _ _ _ H1)).
Qed.
Lemma shbytes_present : forall ly (H : word -> bool) mem a,
Forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly) -> cell1_ok ly a = true -> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b.
Proof.
intros ly H mem a HM Hc. unfold cell1_ok in Hc.
destruct (cell_lookup (Tfib_const ly) (ANum a)) as [[e w av]|] eqn:HL; [|discriminate].
destruct e; try discriminate. destruct w as [|[|w]]; try discriminate.
destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply Z.eqb_eq in Hc. subst.
pose proof (tfib_const_lookup_x B TB ly H mem a 1 _ HM HL) as Hv.
specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. eexists. exact Hv.
Qed.
Lemma zs_present : forall ly (H : word -> bool) mem a,
(forall r, In r (zero_shadow_ranges B ly) -> zero_shadow (aview tfibsegs H mem) SHADOW_OFF (fst r) (snd r)) ->
zs_cov a = true -> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b.
Proof.
intros ly H mem a HZS Hc. unfold zs_cov in Hc. apply existsb_exists in Hc as ([lo len] & Hin & Hc).
apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbn [fst snd] in H1, H2.
pose proof (HZS (lo, len)
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh _ TB); exact Hin)) as HZ.
specialize (HZ (a - shadow_of_addr SHADOW_OFF lo) ltac:(cbn [fst snd]; lia)). cbn [fst snd] in HZ.
replace (shadow_of_addr SHADOW_OFF lo + (a - shadow_of_addr SHADOW_OFF lo)) with a in HZ by lia.
unfold aview in HZ. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [exists b; reflexivity | discriminate].
Qed.
Lemma shw_ok : forall ly (H : word -> bool) mem E,
Forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly) ->
(forall r, In r (zero_shadow_ranges B ly) -> zero_shadow (aview tfibsegs H mem) SHADOW_OFF (fst r) (snd r)) ->
Forall (region_ok tfibsegs E (mrestrict H mem)) (map shw_region x2_shw).
Proof.
intros ly H mem E HM HZS. apply Forall_map. apply Forall_forall. intros [lo n] Hin.
pose proof (shbyte_chk_true ly) as Hc. unfold shbyte_chk in Hc. rewrite forallb_forall in Hc.
assert (Hr : 0x5fb000 <= lo /\ 0 <= n /\ lo + n <= 2 ^ 47).
{ cbn in Hin. destruct Hin as [Hq|[Hq|[Hq|[Hq|[]]]]]; injection Hq as <- <-; lia. }
unfold shw_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. rewrite Z.add_0_l.
assert (Hb2 : exists b, mbyte tfibsegs (mrestrict H mem) o = Some b).
{ assert (Hx : In o x2_shbytes).
{ unfold x2_shbytes. apply in_flat_map. exists (lo, n). split; [exact Hin|]. cbn [fst snd]. apply In_zrange. rewrite Z2Nat.id by lia. lia. }
specialize (Hc o Hx). apply orb_prop in Hc as [Hc|Hc]; [exact (shbytes_present ly H mem o HM Hc) | exact (zs_present ly H mem o HZS Hc)]. }
destruct Hb2 as [b Hb].
apply (mbyte_high_writable _ o b); [unfold TFIB_IMG_END; lia | exact Hb].
Qed.
Lemma zi8_14ea00 : wseg_ok tfibsegs (Z_to_bv 64 0xa2a00) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma zi8_14f970 : wseg_ok tfibsegs (Z_to_bv 64 0xa3970) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma x2_windows : forall E a, in_wrange E (ss_mem ss_x2) a ->
(bv_unsigned (ew E 2) - X2_STK <= a < bv_unsigned (ew E 2)) \/ XW2 a.
Proof.
intros E a Hin. destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
cbn in Ht. unfold XW2. unfold X2_STK in *.
repeat (destruct Ht as [Hq|Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hr; lia|]). destruct Ht.
Qed.
(* The walk over any allocator invariant ARy that yields the layout, the start-up const cells and the zero-shadow
   ranges (x2_realizes_x takes them from icpt_laws_x, x2_realizes from ARm without AR_laws). *)
Lemma x2_realizes_of_cells : forall (ARy : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop),
(forall ly S Hpx W mem md, ARy ly S Hpx W mem md -> layout_ok ly /\ Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly) /\
(forall r, In r (zero_shadow_ranges B ly) -> zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (fst r) (snd r))) ->
xret_realizes_noar_x B ARy X2_PC XW2 XTRUE.
Proof.
intros ARy HF ly S Hpx W regs mem md HPRE _. pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HES : ESTACK = 4096) by reflexivity.
destruct (HF ly S Hpx W mem md HAR) as (HLY & HM & HZS). pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold cfg_at. change (w64 X2_PC) with (Z_to_bv 64 X2_PC).
set (sp0 := spZ regs) in *.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (E := Ereg regs (@nil word)).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (HS0 : st_ok tfibsegs E ss_x2 (restrict (w_H W) (mkst regs (Z_to_bv 64 X2_PC) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_x2. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold x2_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split; [exact (shw_ok ly _ mem E HM HZS) | exact (rodata_ok ly _ mem E HM)]]]].
+ apply (region_ok_stack tfibsegs E _ 2 sp0 (- X2_STK)); [exact E2 | unfold X2_STK; lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. unfold X2_STK in Ha. lia.
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xa2a00 8); [exact zi8_14ea00 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 1); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup_x B TB ly _ mem 0xa2a00 8 1 HM ltac:(vm_compute; reflexivity)).
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xa3970 8); [exact zi8_14f970 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 0); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup_x B TB ly _ mem 0xa3970 8 0 HM (MU0 ly)).
- apply pairwise_disjoint_of_extents. unfold x2_regions, x2_shw, x2_rodata, cellr, shw_region, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2. unfold X2_STK.
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
Theorem x2_realizes_x : xret_realizes_noar_x B ARx X2_PC XW2 XTRUE.
Proof.
exact (x2_realizes_of_cells ARx (fun ly S Hpx W mem md H => conj (ilx_layout _ _ WL _ _ _ _ _ _ H)
(conj (ilx_const _ _ WL _ _ _ _ _ _ H) (fun r Hr => ilx_zshadow _ _ WL _ _ _ _ _ _ r H Hr)))).
Qed.
End S.
Section SA.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis MU0 : forall ly, cell_lookup (Tfib_const ly) (ANum 0xa3970) = Some (ACell (ANum 0xa3970) 8 (AV (ANum 0))).
Theorem x2_realizes : xret_realizes_noar tfibsegs B X2_PC XW2 XTRUE.
Proof.
exact (xret_realizes_noar_of_x B _ _ _ (x2_realizes_of_cells B TB MU0 (AR_x B)
(fun ly S _ W mem md H => conj (am_layout B ly S _ (proj1 H))
(conj (am_const B ly S _ (proj1 H)) (proj1 (Forall_forall _ _) (am_zshadow B ly S _ (proj1 H))))))).
Qed.
End SA.
End d.
