(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI1i UI59 UI56 YI0x YL0e YI08 YI0c UI3h UI3d.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition RLLVM : Z := ubs2_A_LLVMFuzzerTestOneInput.
Definition RL_MUL : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0xa0).
Definition RL_RFC1 : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0xd4).
Definition RL_LH : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0xec).
Definition RL_CLOSE : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0x11c).
Definition RL_RET0 : Z := Eval vm_compute in (ubs2_A_LLVMFuzzerTestOneInput + 0x124).
Definition RLLVM_FRAME : Z := 128.
Definition RRFC : Z := ubs2_A_read_frameconfig.
Definition RR_M1 : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0xa4).
Definition RR_EPI : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0xf8).
Definition RR_MAL : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0x94).
Definition RR_AMC : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0xe4).
Definition RR_OR : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0xbc).
Definition RR_SEQZ : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 0xf4).
Definition RRFC_FRAME : Z := 80.
Definition RRFC_STK : Z := RRFC_FRAME + ALLOC_STACK.
Definition rsaved_ok (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
word_mem ubs2segs mem (sp0 - 8) (bv_unsigned (getr regs0 1)) /\
word_mem ubs2segs mem (sp0 - 16) (bv_unsigned (getr regs0 8)) /\
word_mem ubs2segs mem (sp0 - 24) (bv_unsigned (getr regs0 9)) /\
word_mem ubs2segs mem (sp0 - 32) (bv_unsigned (getr regs0 18)).

Definition runtouched_ok (regs0 regs1 : bvmap 5 word) : Prop :=
getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4 /\
getr regs1 19 = getr regs0 19 /\ getr regs1 20 = getr regs0 20 /\ getr regs1 21 = getr regs0 21 /\
getr regs1 22 = getr regs0 22 /\ getr regs1 23 = getr regs0 23 /\ getr regs1 24 = getr regs0 24 /\
getr regs1 25 = getr regs0 25 /\ getr regs1 26 = getr regs0 26 /\ getr regs1 27 = getr regs0 27.
Lemma ubs2_rgb_rodata_kept : forall (MR : MR_t) mem mem',
ubs2_rgb_rodata_ok mem -> img_kept ubs2_msyms mem mem' -> ubs2_rgb_rodata_ok mem'.
Proof.
intros MR mem mem' H K a Ha. rewrite <- (H a Ha).
unshelve eapply (proj1 (K a _ _ _ _)).
- split; [vm_compute; discriminate|]. exists (nth 0 (segments_reserved ubs2segs) (0%bv, 0%bv)).
split; [apply nth_In; vm_compute; lia|].
match goal with |- ?lo <= a < ?hi => let l := eval vm_compute in lo in let h := eval vm_compute in hi in change (l <= a < h) end.
unfold SRC2_RO_LO, SRC2_RO_HI in Ha. lia.
- unfold SRC2_RO_LO, SRC2_RO_HI in Ha. unfold static_owned. cbv -[Z.le Z.lt Z.add Z.sub not]. lia.
- unfold SRC2_RO_LO, SRC2_RO_HI in Ha. cbv -[Z.le Z.lt Z.add Z.sub not]. lia.
- unfold SRC2_RO_LO, SRC2_RO_HI in Ha. cbv -[Z.le Z.lt Z.add Z.sub not]. lia.
Qed.
Lemma denot_mul_atoms_r : forall E a b x y,
ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x * y < 2 ^ 64 ->
sv_denot E (SMd M_MUL (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x * y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb) by lia. rewrite zcanon_id by (unfold M64; nia). reflexivity.
Qed.
Lemma rgbfc_obj : forall m dst img fmt b0 b1 b2 b3 b4 b5,
word_mem ubs2segs m dst img -> 0 <= img < 2 ^ 64 ->
val_mem ubs2segs m (dst + 8) 4 fmt -> 0 <= fmt < 2 ^ 32 ->
mbyte ubs2segs m (dst + 12) = Some (Z_to_bv 8 b0) -> mbyte ubs2segs m (dst + 13) = Some (Z_to_bv 8 b1) ->
mbyte ubs2segs m (dst + 14) = Some (Z_to_bv 8 0) -> mbyte ubs2segs m (dst + 15) = Some (Z_to_bv 8 0) ->
mbyte ubs2segs m (dst + 16) = Some (Z_to_bv 8 b2) -> mbyte ubs2segs m (dst + 17) = Some (Z_to_bv 8 b3) ->
mbyte ubs2segs m (dst + 18) = Some (Z_to_bv 8 0) -> mbyte ubs2segs m (dst + 19) = Some (Z_to_bv 8 0) ->
mbyte ubs2segs m (dst + 20) = Some (Z_to_bv 8 b4) -> mbyte ubs2segs m (dst + 21) = Some (Z_to_bv 8 b5) ->
0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 ->
obj_at ubs2segs m dst LAY_RgbFrameConfig [img; fmt; b0 + 256 * b1; b2 + 256 * b3; b4 + 256 * b5].
Proof.
intros m dst img fmt b0 b1 b2 b3 b4 b5 Wi Ri Vf Rf H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 R0 R1 R2 R3 R4 R5.
cbn [obj_at LAY_RgbFrameConfig]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
repeat match goal with |- _ /\ _ => split end; try exact I.
all: try (change (2 ^ (8 * 8)) with (2 ^ 64)); try (change (2 ^ (8 * 4)) with (256 * 256 * 65536)); try (change (2 ^ (8 * 2)) with (256 * 256)); try lia.
- rewrite Z.add_0_r. apply val_mem_word_mem. exact Wi.
- exact Vf.
- apply val_mem_4; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add Pos.succ]; assumption.
- apply val_mem_4; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add Pos.succ]; assumption.
- apply val_mem_2; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add Pos.succ]; assumption.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Definition rllvm_post (regs0 : bvmap 5 word) L A mem md (c' : config) : Prop :=
exists (fx' : FPState) L' A' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (getr regs0 1) mem' (seg_rom ubs2segs)) md' /\
frm_zero (@fp_csr fx') /\
journal ubs2_msyms MR LIB_STACK_RGB (spZ regs0) [] L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\
st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
(forall b, In b (blocks L A) -> In b (blocks L' A')).
Definition rrfc_post (regs : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) L A mem md
(Bb : list (Z * Z)) (st dst N pdata nb cur : Z) (memc : word -> option byte) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (res cur2 : Z),
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 res /\ 0 <= res < 2 ^ 64 /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - RRFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + RGBFC_SIZE) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs2segs mem2 a = mbyte ubs2segs memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs memc (b + i)) /\
word_mem ubs2segs mem2 st pdata /\ word_mem ubs2segs mem2 (st + 8) nb /\
word_mem ubs2segs mem2 (st + 16) cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ Permutation (blocks L2 A2) Bb) \/
(res <> 0 /\ exists img fmt fattr fgen delay,
obj_at ubs2segs mem2 dst LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] /\
(fmt_okb fmt = false -> img = 0) /\ 0 <= img < 2 ^ 64 /\
Permutation (blocks L2 A2) (img_block img fmt N ++ Bb))).
Definition rrfc_spec : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) -> Permutation (blocks Lc Ac) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp ubs2_msyms) ->
getr regs 10 = Z_to_bv 64 st -> getr regs 11 = Z_to_bv 64 dst -> getr regs 12 = Z_to_bv 64 N ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RRFC_STK -> spZ regs <= st -> st + 24 <= sp0 ->
spZ regs <= dst -> dst + RGBFC_SIZE <= sp0 -> (st + 24 <= dst \/ dst + RGBFC_SIZE <= st) -> st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= RGB_NMAX -> 0 <= cur <= nb -> 0 < nb ->
word_mem ubs2segs memc st pdata -> word_mem ubs2segs memc (st + 8) nb -> word_mem ubs2segs memc (st + 16) cur ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_read_frameconfig) memc (seg_rom ubs2segs)) mdc)
(rrfc_post regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc).
End S.
End c.
