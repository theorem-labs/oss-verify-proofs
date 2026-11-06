(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan). Seg D of the __asan_stack_malloc_8
   walk: `sm8_segD` of lib/A/Rt/StackMalloc8Cuts.v, from PC_POISON_SHADOW (entered by the jal at
   PC_SM8_MSRET - 4) to the return to the caller's ra. *)

(*   The proof has two parts, joined by SRr_bind in `sm8_segD_holds`:
   - `sm8d_call`: the PoisonShadow call, consumed through the summary `poison_shadow_realizes` of
     lib/Reusable/AsStackLeaf.v (the Section hypothesis HPS; a Theorem Labs lane owns its proof). It is the ONLY lemma that
     uses the summary: it turns the summary's post plus the facts of sm8_midCD into `sm8_midD`, the state at
     PC_SM8_MSRET. If the summary's form changes, only this lemma changes.
   - `sm8d_ret`: the epilogue PC_SM8_MSRET .. PC_SM8_MSRET + 28, stepped concretely. The eight instructions are
     read from the image through a code table built at PC_SM8_MSRET (no literal address in this file):
       +0  mv a0, s2          +4  ld ra, 40(sp)     +8  ld s0, 32(sp)     +12 ld s1, 24(sp)
       +16 ld s2, 16(sp)      +20 ld s3, 8(sp)      +24 addi sp, sp, 48   +28 ret
     It writes no memory, so every memory clause of the contract comes from sm8_midD unchanged.
   This is the ending of cgif_rgb_fuzzer's class-7 walk (lib/YF9c.v:356-515, the memset stretch, the return and the
   post), with the inline PoisonShadow walk replaced by the summary and AR closed at the end of Seg C (sm8_midCD).

   No start-up / constant-cell fact is needed here: PoisonShadow's cells are inside the summary's proof, and the
   epilogue reads only the five words the prologue saved (sm8_saved). No import of A/AB01, A/AB03, YB01, YB03,
   A/AD2j, YD2j, A/AD1k, YB05, A/AF0m, YF0m (nor of any lib/A file that imports them). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK14 YA0o YP02 YN01 YG0s YG0q YF0v YG05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YO0d YO0f.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 AsStackSz.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require Import StackMalloc8Tbl StackMalloc8Cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Ltac sm8d_refl := lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end.
Local Ltac m8g := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].

(* The epilogue's code: a table of the 8 instruction words at PC_SM8_MSRET. *)
Definition sm8d_tbl : ctable := Eval vm_compute in build_table tfibsegs PC_SM8_MSRET 8 TEmpty.
Lemma sm8d_tbl_eq : sm8d_tbl = build_table tfibsegs PC_SM8_MSRET 8 TEmpty.
Proof. vm_cast_no_check (eq_refl sm8d_tbl). Qed.
Lemma sm8d_tbl_ok : table_ok tfibsegs sm8d_tbl.
Proof. rewrite sm8d_tbl_eq. apply build_table_ok0. unfold PC_SM8_MSRET. lia. Qed.
Definition sm8d_w (off : Z) : bv 32 :=
Z_to_bv 32 (match clookup sm8d_tbl (PC_SM8_MSRET + off) with Some w => w | None => 0 end).
Lemma sm8d_fetch : forall off, off = 0 \/ off = 4 \/ off = 8 \/ off = 12 \/ off = 16 \/ off = 20 \/ off = 24 \/ off = 28 ->
fetch_word tfibsegs (Z_to_bv 64 (PC_SM8_MSRET + off)) = Some (sm8d_w off).
Proof.
intros off Hoff. unfold sm8d_w. apply (sm8d_tbl_ok (PC_SM8_MSRET + off)).
destruct Hoff as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma sm8d_nec : forall off, off = 0 \/ off = 4 \/ off = 8 \/ off = 12 \/ off = 16 \/ off = 20 \/ off = 24 \/ off = 28 ->
is_ecall (sm8d_w off) = false.
Proof. intros off Hoff. destruct Hoff as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity. Qed.
Lemma sm8d_d0 : decode_any (sm8d_w 0) = Some (OpImm ALU_ADD 10%bv 18%bv 0%bv, 4%Z). Proof. sm8d_refl. Qed.
Lemma sm8d_d4 : decode_any (sm8d_w 4) = Some (Load SZ8 true 1%bv 2%bv 40%bv, 4%Z). Proof. sm8d_refl. Qed.
Lemma sm8d_d8 : decode_any (sm8d_w 8) = Some (Load SZ8 true 8%bv 2%bv 32%bv, 4%Z). Proof. sm8d_refl. Qed.
Lemma sm8d_d12 : decode_any (sm8d_w 12) = Some (Load SZ8 true 9%bv 2%bv 24%bv, 4%Z). Proof. sm8d_refl. Qed.
Lemma sm8d_d16 : decode_any (sm8d_w 16) = Some (Load SZ8 true 18%bv 2%bv 16%bv, 4%Z). Proof. sm8d_refl. Qed.
Lemma sm8d_d20 : decode_any (sm8d_w 20) = Some (Load SZ8 true 19%bv 2%bv 8%bv, 4%Z). Proof. sm8d_refl. Qed.
Lemma sm8d_d24 : decode_any (sm8d_w 24) = Some (OpImm ALU_ADD 2%bv 2%bv 48%bv, 4%Z). Proof. sm8d_refl. Qed.
Lemma sm8d_d28 : decode_any (sm8d_w 28) = Some (Jalr 0%bv 1%bv 0%bv, 4%Z). Proof. sm8d_refl. Qed.
Lemma sm8d_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma sm8d_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia. Qed.
Lemma sm8d_vaddi : forall a k, v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. apply bv_wrap_add_idemp_l. Qed.
Lemma sm8d_rdword_ext : forall (rd rd' : reader) a,
(forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a Hk. unfold rdword.
replace (rd' a) with (rd a) by (rewrite <- (Z.add_0_r a); symmetry; apply Hk; lia).
rewrite !Hk by lia. reflexivity.
Qed.
Lemma sm8d_sm_inv : forall cid S pos S',
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
exists hint', fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S))) = Some (pos, hint') /\
S' = set_fs (mkFS (zupd cid hint' (fs_hint (st_fs S))) ((cid, pos) :: fs_live (st_fs S))) S.
Proof.
intros cid S pos S' H. unfold stack_malloc, bind, get, put, ret in H. cbn [ibind] in H.
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S)))) as [[p h']|] eqn:Hp.
- cbn [ibind apath] in H. injection H as <- <-. exists h'. split; reflexivity.
- cbn [apath] in H. discriminate H.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma sm8d_aview_byte : forall H mem a v,
aview tfibsegs H mem a = Some v -> exists b : byte, mbyte tfibsegs (mrestrict H mem) a = Some b /\ v = bv_unsigned b /\ 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. exists b. split; [reflexivity|]. split; [reflexivity|].
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
Lemma sm8d_aview_some : forall H mem a, apresent H mem a -> aview tfibsegs H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
(* A word the reader sees is a word the machine's ld reads (copied from lib/A/AE2y.v:124, val_mem_of_rdword). *)
Lemma sm8d_word_mem : forall H mem a v,
rdword (aview tfibsegs H mem) a = Some v -> YO0d.word_mem tfibsegs (mrestrict H mem) a v.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview tfibsegs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview tfibsegs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview tfibsegs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview tfibsegs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview tfibsegs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview tfibsegs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview tfibsegs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview tfibsegs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply sm8d_aview_byte in E0 as (c0 & M0 & -> & R0). apply sm8d_aview_byte in E1 as (c1 & M1 & -> & R1).
apply sm8d_aview_byte in E2 as (c2 & M2 & -> & R2). apply sm8d_aview_byte in E3 as (c3 & M3 & -> & R3).
apply sm8d_aview_byte in E4 as (c4 & M4 & -> & R4). apply sm8d_aview_byte in E5 as (c5 & M5 & -> & R5).
apply sm8d_aview_byte in E6 as (c6 & M6 & -> & R6). apply sm8d_aview_byte in E7 as (c7 & M7 & -> & R7).
rewrite ?Z.add_0_r in M0.
set (v := bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))).
assert (Hv : 0 <= v < 2 ^ 64) by (subst v; lia).
assert (BY : forall (k : nat) (c : byte) (lo : Z) (hi : Z),
v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
Z_to_bv 8 (YO0f.le_byte v 8 k) = c).
{ intros k c lo hi Hdec Hlo Hhi. unfold YO0f.le_byte. rewrite (Z.mod_small v) by (cbn; lia).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. change (2 ^ 8) with 256 in Hc.
replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
2:{ apply Z.div_unique with (r := lo); [left; lia | lia]. }
replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
2:{ apply Z.mod_unique with (q := hi); [left; lia | lia]. }
apply Z_to_bv_bv_unsigned. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia];
[ change (a + Z.of_nat 0) with (a + 0); rewrite Z.add_0_r
| change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2 | change (Z.of_nat 3) with 3 | change (Z.of_nat 4) with 4
| change (Z.of_nat 5) with 5 | change (Z.of_nat 6) with 6 | change (Z.of_nat 7) with 7 ].
- rewrite M0. f_equal. symmetry. apply (BY 0%nat c0 0 (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))); cbn; subst v; lia.
- rewrite M1. f_equal. symmetry. apply (BY 1%nat c1 (bv_unsigned c0) (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))))); cbn; subst v; lia.
- rewrite M2. f_equal. symmetry. apply (BY 2%nat c2 (bv_unsigned c0 + 256 * bv_unsigned c1) (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))); cbn; subst v; lia.
- rewrite M3. f_equal. symmetry. apply (BY 3%nat c3 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * bv_unsigned c2))
(bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))); cbn; subst v; lia.
- rewrite M4. f_equal. symmetry. apply (BY 4%nat c4 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * bv_unsigned c3)))
(bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))); cbn; subst v; lia.
- rewrite M5. f_equal. symmetry. apply (BY 5%nat c5 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * bv_unsigned c4))))
(bv_unsigned c6 + 256 * bv_unsigned c7)); cbn; subst v; lia.
- rewrite M6. f_equal. symmetry. apply (BY 6%nat c6 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * bv_unsigned c5)))))
(bv_unsigned c7)); cbn; subst v; lia.
- rewrite M7. f_equal. symmetry. apply (BY 7%nat c7 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * bv_unsigned c6))))))
0); cbn; subst v; lia.
Qed.
(* One `ld rd, imm(sp)` of the epilogue, reading a word the reader sees. *)
Lemma sm8d_ld : forall (H : word -> bool) (memX : word -> option byte) (regsX : bvmap 5 word) (pc : Z) (w : bv 32)
(rd : bv 5) (imm : bv 12) (a z : Z),
fetch_word tfibsegs (Z_to_bv 64 pc) = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ8 true rd 2%bv imm, 4%Z) -> bv_eqb rd 0%bv = false ->
v_addi (getr regsX 2) (bv_signed imm) = Z_to_bv 64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs H memX) a = Some z ->
RiscvSemantics.step tfibsegs (mkst regsX (Z_to_bv 64 pc) (mrestrict H memX) (seg_rom tfibsegs)) =
MachineOk (mkst (regupd regsX rd (Z_to_bv 64 z)) (Z_to_bv 64 (pc + 4)) (mrestrict H memX) (seg_rom tfibsegs)).
Proof.
intros H memX regsX pc w rd imm a z Hf He Hd Hrd Ha Ha0 Ha8 Hw.
destruct (word_mem_ld tfibsegs (mrestrict H memX) a z (sm8d_word_mem H memX a z Hw) Ha0 Ha8) as (bs & Hbs & Hle).
rewrite (step_ld tfibsegs regsX (Z_to_bv 64 pc) (mrestrict H memX) (seg_rom tfibsegs) w rd 2%bv imm bs (Z_to_bv 64 z) Hf He Hd);
[| rewrite Ha; exact Hbs | exact Hle].
rewrite Hrd, sm8d_vaddi. reflexivity.
Qed.

(* The register files of the epilogue, one per instruction. *)
Definition sm8d_r1 (regsP : bvmap 5 word) (fr : Z) : bvmap 5 word := regupd regsP 10%bv (w64 fr).
Definition sm8d_r2 (regs regsP : bvmap 5 word) (fr : Z) : bvmap 5 word := regupd (sm8d_r1 regsP fr) 1%bv (getr regs 1).
Definition sm8d_r3 (regs regsP : bvmap 5 word) (fr : Z) : bvmap 5 word := regupd (sm8d_r2 regs regsP fr) 8%bv (getr regs 8).
Definition sm8d_r4 (regs regsP : bvmap 5 word) (fr : Z) : bvmap 5 word := regupd (sm8d_r3 regs regsP fr) 9%bv (getr regs 9).
Definition sm8d_r5 (regs regsP : bvmap 5 word) (fr : Z) : bvmap 5 word := regupd (sm8d_r4 regs regsP fr) 18%bv (getr regs 18).
Definition sm8d_r6 (regs regsP : bvmap 5 word) (fr : Z) : bvmap 5 word := regupd (sm8d_r5 regs regsP fr) 19%bv (getr regs 19).
Definition sm8d_r7 (regs regsP : bvmap 5 word) (fr : Z) : bvmap 5 word := regupd (sm8d_r6 regs regsP fr) 2%bv (getr regs 2).

Section e.
Variable B : asyms.
(* The PoisonShadow summary of lib/Reusable/AsStackLeaf.v at scene's PoisonShadow (a Theorem Labs lane proves it). *)
Hypothesis HPS : poison_shadow_realizes tfibsegs B PC_POISON_SHADOW.

(* The state at PC_SM8_MSRET, after PoisonShadow returns: what the epilogue needs, and the contract's memory
   clauses, which the epilogue (no store) carries unchanged. *)
Definition sm8_midD (ly : alayout) (S S' : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n pos : Z)
(regsP : bvmap 5 word) (memP : word -> option byte) (mdP : Model) : Prop :=
AR tfibsegs B ly S' W memP mdP /\
getr regsP 2 = w64 (spZ regs - SM8_FRAME) /\
getr regsP 18 = w64 (frame_addr ly CID8 pos) /\
sm8_regs_kept regs regsP /\ sm8_saved W regs memP /\ same_but_materialized md mdP /\
zero_shadow (aview tfibsegs (w_H W) memP) SHADOW_OFF (frame_addr ly CID8 pos) n /\
rdword (aview tfibsegs (w_H W) memP) (frame_addr ly CID8 pos + fs_frame_bytes CID8 - 8)
= Some (flag_addr ly CID8 pos) /\
(forall a, frame_addr ly CID8 pos <= a < frame_addr ly CID8 pos + fs_frame_bytes CID8 ->
apresent (w_H W) memP a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a ->
~ (spZ regs - ESTACK <= a < spZ regs) ->
aview tfibsegs (w_H W) memP a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) memP a).

Lemma sm8d_AR_sbm : forall ly S W mem md md',
AR tfibsegs B ly S W mem md -> same_but_materialized md md' -> AR tfibsegs B ly S W mem md'.
Proof.
intros ly S W mem md md' (M & L & B0 & MW & HS) Hs. rewrite (same_but_materialized_wvb md md' Hs).
split; [exact M|]. split; [|split; [exact B0 | split; [|exact HS]]].
- eapply ALedger_same; [exact L | reflexivity | reflexivity | reflexivity].
- apply (amwf_same md); [reflexivity | reflexivity | exact MW].
Qed.

(* The PoisonShadow call (PC_POISON_SHADOW, a0 = frame, a1 = n, a2 = 0, ra = PC_SM8_MSRET), through HPS. *)
Lemma sm8d_call : forall ly S W regs mem md pos S' n regs3 mem3 md3,
sm8_entry B ly S W regs mem md pos S' n ->
sm8_midCD B ly S S' W regs mem md n pos regs3 mem3 md3 ->
SRr tfibsegs W (cfg_at tfibsegs PC_POISON_SHADOW regs3 mem3 md3)
(fun W' c' => W' = W /\ exists regsP memP mdP,
c' = cfg_at tfibsegs PC_SM8_MSRET regsP memP mdP /\ sm8_midD ly S S' W regs mem md n pos regsP memP mdP).
Proof.
intros ly S W regs mem md pos S' n regs3 mem3 md3 HE HCD.
destruct HE as (HPRE & Hn & Hrng & Hmod & Hcnt & Hpath).
destruct HPRE as (HAR & Hra & Hal & Hslo & Hshi & HpresE & Hgp & Htp).
destruct HCD as (HAR3 & R1 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & Hpos & KEEP3 & SAV3 & SPRES3 & SBM3 & MEQ3 & FLAG3 & FPRES3 & SHPRES3).
pose proof (proj1 HAR) as M.
pose proof (am_layout _ _ _ _ M) as LO.
pose proof (lo_top _ LO) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as FA.
cbn [fst snd] in FA. pose proof FA as [FA0 FAZ].
pose proof ASAN_CEIL_range as [CR _].
unfold ESTACK in Hslo, HpresE.
assert (HC8 : CID8 = 8) by reflexivity.
assert (HFB : fs_frame_bytes CID8 = 16384) by reflexivity.
assert (HFN : fs_frames CID8 = 64) by reflexivity.
assert (HFF : frame_addr ly CID8 pos = ly_F ly + 8425472 + pos * 16384).
{ unfold frame_addr, fs_frame_off, fs_frame_bytes, kFakeFramesOff, CID8, kStackSizeLog.
change (Z.shiftl 1 20) with 1048576. change (Z.shiftl 64 8) with 16384. lia. }
assert (HFL : flag_addr ly CID8 pos = ly_F ly + 36736 + pos).
{ unfold flag_addr, fs_flag_off. change (kFakeFlagsOff + fs_flags_off CID8) with 36736. lia. }
assert (Hp64 : 0 <= pos < 64) by (rewrite <- HFN; exact Hpos).
assert (HFF8 : frame_addr ly CID8 pos mod 8 = 0).
{ apply (proj2 (Z.mod_divide _ 8 ltac:(lia))). exists (512 * (ly_F ly / 4096) + 1053184 + pos * 2048).
pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)) as D. rewrite FAL, Z.add_0_r in D. lia. }
assert (HFFin : ly_F ly <= frame_addr ly CID8 pos /\ frame_addr ly CID8 pos + 16384 <= ly_F ly + kFakeStackSize)
by (unfold kFakeStackSize; lia).
assert (HFFhi : frame_addr ly CID8 pos + 16384 <= kHighMemEnd).
{ clear - FAZ CR HFFin. unfold kFakeStackSize, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *. lia. }
assert (FFA : in_app (frame_addr ly CID8 pos) 16384).
{ apply (in_app_sub (ly_F ly) kFakeStackSize); [exact FA | lia | lia | lia]. }
pose proof (shadow_range_below (frame_addr ly CID8 pos) 16384 ltac:(lia) ltac:(lia) HFFhi) as SHB.
change (16384 / 8) with 2048 in SHB.
assert (SPB : kHighMemBeg + 4096 <= spZ regs <= kHighMemEnd) by lia.
assert (OEB : forall a, frame_addr ly CID8 pos <= a < frame_addr ly CID8 pos + 16384 ->
~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_zr a (ly_img ly)).
{ intros a Ha.
assert (EX : Exists (in_zr a) (owned_extents ly)).
{ apply Exists_exists. exists (ly_F ly, kFakeStackSize). split; [unfold owned_extents; cbn; tauto|].
unfold in_zr; cbn [fst snd]. lia. }
destruct (owned_extents_bound ly a LO EX) as (_ & X1 & X2). split; assumption. }
unfold kHighMemBeg, kHighMemEnd in SPB, SHB, HFFhi, Lbeg, Lhi.
assert (NIN : ~ In (CID8, pos) (frames S)).
{ destruct (sm8d_sm_inv CID8 S pos S' Hpath) as (hint' & Hprobe & _).
assert (HN0 : 0 < fs_frames CID8) by (rewrite HFN; lia).
destruct (fs_probe_some _ _ _ _ _ _ HN0 Hprobe) as (h & _ & _ & _ & Hm).
unfold frames. exact (mem_pos_false _ _ _ Hm). }
assert (OWNF : forall a, frame_addr ly CID8 pos <= a < frame_addr ly CID8 pos + fs_frame_bytes CID8 -> aowned B ly S a).
{ intros a Ha. exact (own_free_frame B ly S _ CID8 pos a M ltac:(rewrite HC8; lia) Hpos NIN Ha). }
assert (OWNSH : forall a, shadow_addr (frame_addr ly CID8 pos) <= a < shadow_addr (frame_addr ly CID8 pos) + fs_frame_bytes CID8 / 8 ->
aowned B ly S a).
{ intros a Ha. exact (own_free_frame_shadow B ly S _ CID8 pos a M ltac:(rewrite HC8; lia) Hpos NIN Ha). }
assert (OWNLOW : forall a, ly_F ly <= a < ly_F ly + kFakeFramesOff -> aowned B ly S a).
{ intros a Ha. exact (own_F_low B ly S _ a M Ha). }
assert (HN8 : 0 < n / 8 <= 2048).
{ split; [apply Z.div_str_pos; lia | apply Z.div_le_upper_bound; lia]. }
assert (SP3 : spZ regs3 = spZ regs - 48).
{ unfold spZ at 1. rewrite R2. unfold SM8_FRAME, w64. apply sm8d_u. lia. }
eapply SRr_mono.
{ refine (HPS ly S' W regs3 mem3 md3 CID8 pos (frame_addr ly CID8 pos) n 0 HAR3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
- rewrite R1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
- rewrite SP3. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- rewrite SP3. unfold PS_STK. lia.
- rewrite SP3. lia.
- intros a Ha. rewrite SP3 in Ha. unfold PS_STK in Ha. apply SPRES3. unfold ESTACK. lia.
- pose proof (KEEP3 3 ltac:(lia)) as K3. replace (Z_to_bv 5 3) with (3%bv : bv 5) in K3 by (apply bv_eq; reflexivity).
rewrite K3. exact Hgp.
- pose proof (KEEP3 4 ltac:(lia)) as K4. replace (Z_to_bv 5 4) with (4%bv : bv 5) in K4 by (apply bv_eq; reflexivity).
rewrite K4. exact Htp.
- rewrite HC8. lia.
- exact Hpos.
- exact R10.
- exact R11.
- exact R12.
- lia.
- lia.
- exact Hmod.
- exact HFF8.
- lia.
- lia.
- intros a Ha. apply SHPRES3. rewrite HFB. change (16384 / 8) with 2048. lia. }
intros W' c' _ (-> & regsP & memP & mdP & -> & HARP & PRESP & SBMP & ZSHP & MEQP & STKP).
rewrite SP3 in MEQP, STKP. unfold PS_STK in MEQP, STKP.
assert (RA3 : raZ regs3 = PC_SM8_MSRET).
{ unfold raZ. rewrite R1. unfold w64. apply sm8d_u. unfold PC_SM8_MSRET. lia. }
split; [reflexivity|]. exists regsP, memP, mdP. rewrite RA3. split; [reflexivity|].
assert (KEEPSTK : forall a, spZ regs - 48 <= a < spZ regs -> aview tfibsegs (w_H W) memP a = aview tfibsegs (w_H W) mem3 a).
{ intros a Ha. apply MEQP; lia. }
assert (KEEPFR : forall a, frame_addr ly CID8 pos <= a < frame_addr ly CID8 pos + 16384 ->
aview tfibsegs (w_H W) memP a = aview tfibsegs (w_H W) mem3 a).
{ intros a Ha. destruct (OEB a Ha) as [NS _]. apply MEQP; [lia | | lia].
intros Hs. apply (app_vs_shadow _ _ _ _ a FFA FFA ltac:(lia) Ha). change (16384 / 8) with 2048. lia. }
unfold sm8_midD.
split; [exact HARP|].
split.
{ pose proof (PRESP 2 ltac:(unfold acallee_saved; lia)) as P2.
replace (Z_to_bv 5 2) with (2%bv : bv 5) in P2 by (apply bv_eq; reflexivity). rewrite P2. exact R2. }
split.
{ pose proof (PRESP 18 ltac:(unfold acallee_saved; lia)) as P18.
replace (Z_to_bv 5 18) with (18%bv : bv 5) in P18 by (apply bv_eq; reflexivity). rewrite P18. exact R18. }
split.
{ intros r Hr. rewrite (PRESP r ltac:(unfold acallee_saved; lia)). exact (KEEP3 r Hr). }
split.
{ destruct SAV3 as (S8 & S16 & S24 & S32 & S40).
assert (KS : forall x, spZ regs - 48 <= x -> x + 8 <= spZ regs ->
rdword (aview tfibsegs (w_H W) memP) x = rdword (aview tfibsegs (w_H W) mem3) x).
{ intros x X1 X2. apply sm8d_rdword_ext. intros k Hk. apply KEEPSTK. lia. }
unfold sm8_saved. rewrite !KS by lia. exact (conj S8 (conj S16 (conj S24 (conj S32 S40)))). }
split; [exact (same_but_materialized_trans md md3 mdP SBM3 SBMP)|].
split; [intros i Hi; exact (ZSHP i Hi)|].
split.
{ rewrite <- FLAG3. apply sm8d_rdword_ext. intros k Hk. apply KEEPFR. rewrite HFB. lia. }
split.
{ intros a Ha. rewrite HFB in Ha. destruct (OEB a Ha) as [_ NI].
eapply aview_present; [exact (proj1 (proj2 HARP)) | lia | exact NI |].
rewrite (KEEPFR a Ha). apply sm8d_aview_some. apply FPRES3. rewrite HFB. exact Ha. }
split.
{ intros a Ha NS NS' NE. unfold ESTACK in NE.
assert (NSH : ~ (shadow_addr (frame_addr ly CID8 pos) <= a < shadow_addr (frame_addr ly CID8 pos) + n / 8)).
{ intros Hs. apply NS. apply OWNSH. rewrite HFB. change (16384 / 8) with 2048. lia. }
rewrite (MEQP a Ha NSH ltac:(lia)).
apply MEQ3; [exact Ha | unfold SM8_WIN; lia | | | ].
- intros Hh. apply NS. apply OWNLOW. unfold kFakeFramesOff. lia.
- intros Ef. apply NS. apply OWNLOW. rewrite Ef, HFL. unfold kFakeFramesOff. lia.
- intros Hf. apply NS. apply OWNF. exact Hf. }
assert (NIMG : forall a, spZ regs - 4096 <= a -> ~ in_zr a (ly_img ly)).
{ intros a Ha Hi. pose proof (lo_img _ LO) as (I0 & _ & I2 & _). unfold in_zr in Hi. unfold kImgLo, kImgEnd in *. lia. }
assert (PRESX : forall a, spZ regs - 4096 <= a < spZ regs -> ~ (spZ regs - 48 - 256 <= a < spZ regs - 48) ->
apresent (w_H W) memP a).
{ intros a Ha Hw. eapply aview_present; [exact (proj1 (proj2 HARP)) | lia | exact (NIMG a (proj1 Ha)) |].
rewrite (MEQP a ltac:(lia) ltac:(lia) Hw). apply sm8d_aview_some. apply SPRES3. unfold ESTACK. lia. }
intros a Ha. unfold ESTACK in Ha.
destruct (Z_lt_le_dec a (spZ regs - 48 - 256)) as [L1|L1]; [apply PRESX; lia|].
destruct (Z_lt_le_dec a (spZ regs - 48)) as [L2|L2]; [apply STKP; lia | apply PRESX; lia].
Qed.

(* The epilogue: a0 := frame, ra/s0/s1/s2/s3 := the saved words, sp := sp0, ret. *)
Lemma sm8d_ret : forall ly S W regs mem md pos S' n regsP memP mdP,
sm8_entry B ly S W regs mem md pos S' n ->
sm8_midD ly S S' W regs mem md n pos regsP memP mdP ->
SRr tfibsegs W (cfg_at tfibsegs PC_SM8_MSRET regsP memP mdP)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S' W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly CID8 pos) /\
zero_shadow (aview tfibsegs (w_H W) mem') SHADOW_OFF (frame_addr ly CID8 pos) n /\
rdword (aview tfibsegs (w_H W) mem') (frame_addr ly CID8 pos + fs_frame_bytes CID8 - 8)
= Some (flag_addr ly CID8 pos) /\
(forall a, frame_addr ly CID8 pos <= a < frame_addr ly CID8 pos + fs_frame_bytes CID8 ->
apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a ->
~ (spZ regs - ESTACK <= a < spZ regs) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md pos S' n regsP memP mdP HE HD.
destruct HE as (HPRE & _ & _ & _ & _ & _).
destruct HPRE as (HAR & Hra & _ & Hslo & Hshi & _ & _ & _).
destruct HD as (HARP & P2 & P18 & KEEP & SAV & SBM & ZSH & FLAG & FPRES & MEQ & SPRES).
destruct SAV as (S8 & S16 & S24 & S32 & S40).
unfold YK0s.ret_ok in Hra.
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO.
pose proof (lo_top _ LO) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
unfold ESTACK in Hslo.
assert (SPB : kHighMemBeg + 4096 <= spZ regs <= kHighMemEnd) by lia.
unfold kHighMemBeg, kHighMemEnd in SPB.
pose proof (sm8d_fetch 0 ltac:(lia)) as F0. rewrite Z.add_0_r in F0.
pose proof (sm8d_fetch 4 ltac:(lia)) as F4. pose proof (sm8d_fetch 8 ltac:(lia)) as F8.
pose proof (sm8d_fetch 12 ltac:(lia)) as F12. pose proof (sm8d_fetch 16 ltac:(lia)) as F16.
pose proof (sm8d_fetch 20 ltac:(lia)) as F20. pose proof (sm8d_fetch 24 ltac:(lia)) as F24.
pose proof (sm8d_fetch 28 ltac:(lia)) as F28.
pose proof (sm8d_nec 0 ltac:(lia)) as E0. pose proof (sm8d_nec 4 ltac:(lia)) as E4.
pose proof (sm8d_nec 8 ltac:(lia)) as E8. pose proof (sm8d_nec 12 ltac:(lia)) as E12.
pose proof (sm8d_nec 16 ltac:(lia)) as E16. pose proof (sm8d_nec 20 ltac:(lia)) as E20.
pose proof (sm8d_nec 24 ltac:(lia)) as E24. pose proof (sm8d_nec 28 ltac:(lia)) as E28.
assert (ST0 : RiscvSemantics.step tfibsegs (mkst regsP (Z_to_bv 64 PC_SM8_MSRET) (mrestrict (w_H W) memP) (seg_rom tfibsegs))
= MachineOk (mkst (sm8d_r1 regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 4)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))).
{ rewrite (step_addi_at tfibsegs regsP (Z_to_bv 64 PC_SM8_MSRET) (mrestrict (w_H W) memP) (seg_rom tfibsegs) (sm8d_w 0)
10%bv 18%bv 0%bv (w64 (frame_addr ly CID8 pos)) F0 E0 sm8d_d0 ltac:(reflexivity)).
- rewrite sm8d_vaddi. reflexivity.
- rewrite P18. change (bv_signed (0%bv : bv 12)) with 0. apply v_addi_0. }
assert (A1 : v_addi (getr (sm8d_r1 regsP (frame_addr ly CID8 pos)) 2) (bv_signed (40%bv : bv 12)) = Z_to_bv 64 (spZ regs - 8)).
{ unfold sm8d_r1. m8g. rewrite P2. change (bv_signed (40%bv : bv 12)) with 40. unfold w64, SM8_FRAME. rewrite sm8d_vaddi. f_equal. lia. }
assert (ST1 : RiscvSemantics.step tfibsegs (mkst (sm8d_r1 regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 4)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))
= MachineOk (mkst (sm8d_r2 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 8)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))).
{ rewrite (sm8d_ld (w_H W) memP (sm8d_r1 regsP (frame_addr ly CID8 pos)) (PC_SM8_MSRET + 4) (sm8d_w 4) 1%bv 40%bv (spZ regs - 8) (raZ regs)
F4 E4 sm8d_d4 ltac:(reflexivity) A1 ltac:(lia) ltac:(lia) S8).
unfold raZ. rewrite Z_to_bv_bv_unsigned. replace (PC_SM8_MSRET + 4 + 4) with (PC_SM8_MSRET + 8) by lia. reflexivity. }
assert (A2 : v_addi (getr (sm8d_r2 regs regsP (frame_addr ly CID8 pos)) 2) (bv_signed (32%bv : bv 12)) = Z_to_bv 64 (spZ regs - 16)).
{ unfold sm8d_r2, sm8d_r1. m8g. rewrite P2. change (bv_signed (32%bv : bv 12)) with 32. unfold w64, SM8_FRAME. rewrite sm8d_vaddi. f_equal. lia. }
assert (ST2 : RiscvSemantics.step tfibsegs (mkst (sm8d_r2 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 8)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))
= MachineOk (mkst (sm8d_r3 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 12)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))).
{ rewrite (sm8d_ld (w_H W) memP (sm8d_r2 regs regsP (frame_addr ly CID8 pos)) (PC_SM8_MSRET + 8) (sm8d_w 8) 8%bv 32%bv (spZ regs - 16)
(bv_unsigned (getr regs 8)) F8 E8 sm8d_d8 ltac:(reflexivity) A2 ltac:(lia) ltac:(lia) S16).
rewrite Z_to_bv_bv_unsigned. replace (PC_SM8_MSRET + 8 + 4) with (PC_SM8_MSRET + 12) by lia. reflexivity. }
assert (A3 : v_addi (getr (sm8d_r3 regs regsP (frame_addr ly CID8 pos)) 2) (bv_signed (24%bv : bv 12)) = Z_to_bv 64 (spZ regs - 24)).
{ unfold sm8d_r3, sm8d_r2, sm8d_r1. m8g. rewrite P2. change (bv_signed (24%bv : bv 12)) with 24. unfold w64, SM8_FRAME. rewrite sm8d_vaddi. f_equal. lia. }
assert (ST3 : RiscvSemantics.step tfibsegs (mkst (sm8d_r3 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 12)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))
= MachineOk (mkst (sm8d_r4 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 16)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))).
{ rewrite (sm8d_ld (w_H W) memP (sm8d_r3 regs regsP (frame_addr ly CID8 pos)) (PC_SM8_MSRET + 12) (sm8d_w 12) 9%bv 24%bv (spZ regs - 24)
(bv_unsigned (getr regs 9)) F12 E12 sm8d_d12 ltac:(reflexivity) A3 ltac:(lia) ltac:(lia) S24).
rewrite Z_to_bv_bv_unsigned. replace (PC_SM8_MSRET + 12 + 4) with (PC_SM8_MSRET + 16) by lia. reflexivity. }
assert (A4 : v_addi (getr (sm8d_r4 regs regsP (frame_addr ly CID8 pos)) 2) (bv_signed (16%bv : bv 12)) = Z_to_bv 64 (spZ regs - 32)).
{ unfold sm8d_r4, sm8d_r3, sm8d_r2, sm8d_r1. m8g. rewrite P2. change (bv_signed (16%bv : bv 12)) with 16. unfold w64, SM8_FRAME. rewrite sm8d_vaddi. f_equal. lia. }
assert (ST4 : RiscvSemantics.step tfibsegs (mkst (sm8d_r4 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 16)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))
= MachineOk (mkst (sm8d_r5 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 20)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))).
{ rewrite (sm8d_ld (w_H W) memP (sm8d_r4 regs regsP (frame_addr ly CID8 pos)) (PC_SM8_MSRET + 16) (sm8d_w 16) 18%bv 16%bv (spZ regs - 32)
(bv_unsigned (getr regs 18)) F16 E16 sm8d_d16 ltac:(reflexivity) A4 ltac:(lia) ltac:(lia) S32).
rewrite Z_to_bv_bv_unsigned. replace (PC_SM8_MSRET + 16 + 4) with (PC_SM8_MSRET + 20) by lia. reflexivity. }
assert (A5 : v_addi (getr (sm8d_r5 regs regsP (frame_addr ly CID8 pos)) 2) (bv_signed (8%bv : bv 12)) = Z_to_bv 64 (spZ regs - 40)).
{ unfold sm8d_r5, sm8d_r4, sm8d_r3, sm8d_r2, sm8d_r1. m8g. rewrite P2. change (bv_signed (8%bv : bv 12)) with 8. unfold w64, SM8_FRAME. rewrite sm8d_vaddi. f_equal. lia. }
assert (ST5 : RiscvSemantics.step tfibsegs (mkst (sm8d_r5 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 20)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))
= MachineOk (mkst (sm8d_r6 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 24)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))).
{ rewrite (sm8d_ld (w_H W) memP (sm8d_r5 regs regsP (frame_addr ly CID8 pos)) (PC_SM8_MSRET + 20) (sm8d_w 20) 19%bv 8%bv (spZ regs - 40)
(bv_unsigned (getr regs 19)) F20 E20 sm8d_d20 ltac:(reflexivity) A5 ltac:(lia) ltac:(lia) S40).
rewrite Z_to_bv_bv_unsigned. replace (PC_SM8_MSRET + 20 + 4) with (PC_SM8_MSRET + 24) by lia. reflexivity. }
assert (V6 : v_addi (getr (sm8d_r6 regs regsP (frame_addr ly CID8 pos)) 2) (bv_signed (48%bv : bv 12)) = getr regs 2).
{ unfold sm8d_r6, sm8d_r5, sm8d_r4, sm8d_r3, sm8d_r2, sm8d_r1. m8g. rewrite P2. change (bv_signed (48%bv : bv 12)) with 48.
unfold w64, SM8_FRAME. rewrite sm8d_vaddi. replace (spZ regs - 48 + 48) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
assert (ST6 : RiscvSemantics.step tfibsegs (mkst (sm8d_r6 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 24)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))
= MachineOk (mkst (sm8d_r7 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 28)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))).
{ rewrite (step_addi_at tfibsegs (sm8d_r6 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 24)) (mrestrict (w_H W) memP) (seg_rom tfibsegs)
(sm8d_w 24) 2%bv 2%bv 48%bv (getr regs 2) F24 E24 sm8d_d24 ltac:(reflexivity) V6), sm8d_vaddi.
replace (PC_SM8_MSRET + 24 + 4) with (PC_SM8_MSRET + 28) by lia. reflexivity. }
assert (G71 : getr (sm8d_r7 regs regsP (frame_addr ly CID8 pos)) 1 = getr regs 1).
{ unfold sm8d_r7, sm8d_r6, sm8d_r5, sm8d_r4, sm8d_r3, sm8d_r2. m8g. reflexivity. }
assert (ST7 : RiscvSemantics.step tfibsegs (mkst (sm8d_r7 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 28)) (mrestrict (w_H W) memP) (seg_rom tfibsegs))
= MachineOk (mkst (sm8d_r7 regs regsP (frame_addr ly CID8 pos)) (getr regs 1) (mrestrict (w_H W) memP) (seg_rom tfibsegs))).
{ rewrite (step_jalr_x0 tfibsegs (sm8d_r7 regs regsP (frame_addr ly CID8 pos)) (Z_to_bv 64 (PC_SM8_MSRET + 28)) (mrestrict (w_H W) memP) (seg_rom tfibsegs)
(sm8d_w 28) 1%bv 0%bv (getr regs 1) F28 E28 sm8d_d28 G71).
change (bv_signed (0%bv : bv 12)) with 0. rewrite Hra. reflexivity. }
assert (MS : msteps tfibsegs (mkst regsP (w64 PC_SM8_MSRET) (mrestrict (w_H W) memP) (seg_rom tfibsegs))
(mkst (sm8d_r7 regs regsP (frame_addr ly CID8 pos)) (getr regs 1) (mrestrict (w_H W) memP) (seg_rom tfibsegs))).
{ eapply mst_step; [reflexivity | exact ST0 |]. eapply mst_step; [reflexivity | exact ST1 |].
eapply mst_step; [reflexivity | exact ST2 |]. eapply mst_step; [reflexivity | exact ST3 |].
eapply mst_step; [reflexivity | exact ST4 |]. eapply mst_step; [reflexivity | exact ST5 |].
eapply mst_step; [reflexivity | exact ST6 |]. eapply mst_step; [reflexivity | exact ST7 |].
apply mst_refl. }
unfold cfg_at.
eapply (SRr_msteps tfibsegs sm8d_wx W); [rewrite restrict_mkst_fx; exact MS|].
intros md' Hsbm _.
change (ms_mem (mkst regsP (w64 PC_SM8_MSRET) memP (seg_rom tfibsegs))) with memP.
rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|].
exists (sm8d_r7 regs regsP (frame_addr ly CID8 pos)), memP, md'.
split; [unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact (sm8d_AR_sbm ly S' W memP mdP md' HARP Hsbm)|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ (r = 3 \/ r = 4 \/ 20 <= r <= 27)) by lia.
unfold sm8d_r7, sm8d_r6, sm8d_r5, sm8d_r4, sm8d_r3, sm8d_r2, sm8d_r1.
destruct Hc as [->|[->|[->|[->|[->|Hc]]]]].
- replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). m8g. reflexivity.
- replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). m8g. reflexivity.
- replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). m8g. reflexivity.
- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). m8g. reflexivity.
- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). m8g. reflexivity.
- rewrite <- (KEEP r Hc).
assert (Hc' : r = 3 \/ r = 4 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; m8g; reflexivity. }
split; [exact (same_but_materialized_trans md mdP md' SBM Hsbm)|].
split.
{ unfold sm8d_r7, sm8d_r6, sm8d_r5, sm8d_r4, sm8d_r3, sm8d_r2, sm8d_r1. m8g. reflexivity. }
exact (conj ZSH (conj FLAG (conj FPRES (conj MEQ SPRES)))).
Qed.

Lemma sm8_segD_holds : sm8_segD B.
Proof.
unfold sm8_segD. intros ly S W regs mem md pos S' n regs3 mem3 md3 HE HCD.
eapply SRr_bind; [exact (sm8d_call ly S W regs mem md pos S' n regs3 mem3 md3 HE HCD)|].
intros W1 c1 _ (-> & regsP & memP & mdP & -> & HD).
exact (sm8d_ret ly S W regs mem md pos S' n regsP memP mdP HE HD).
Qed.
End e.
End d.
