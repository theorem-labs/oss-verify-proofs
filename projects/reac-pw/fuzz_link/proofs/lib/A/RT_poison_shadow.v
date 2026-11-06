(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: __asan::PoisonShadow(p, n, v) of the pinned image fuzz_scene.asan
   (libreac/fuzz_scene), entry 0x55bb8, 319 instructions, over the shadow of ONE fake-stack frame. The
   statement is lib/Reusable/AsStackLeaf.v's poison_shadow_realizes (a Theorem Labs lane); nothing of it moves here.

   MEASURED (internal path): the body reaches musl memset
   (tfib_A_musl_memset = 0x94e40) by the tail jump `jr t1` at 0x55f54 with its own 64-byte frame already
   released, and it is a straight line under the premises, except for three branches that the symbolic
   runner cannot settle from the atom facts alone. They are settled here, as conditions (YP06.add_cond)
   with a Coq proof of each:
     0x55bd8 `beqz a2`      v = 0 skips the CanPoisonMemory test   -> c_v0  (only when v = 0)
     0x55df8 `bgeu a4, a1`  p + n - 8 is in the low application zone -> c_end (only in the low zone)
     0x55e70 `bltu s0, a1`  n / 8 < clear_shadow_mmap_threshold      -> c_thr (only when v = 0; for
                            v <> 0 the body jumps over that test at 0x55e60)
   So the walk is four phases over two booleans: hi (the fake stack is in the high application zone, from
   AR's layout) and v0 (v = 0, __asan_stack_malloc_8's call; v <> 0 is __asan_stack_free_8's).

   Every constant cell the body reads is in A/AF0m.v's Tfib_const, so TfibSyms B alone carries them and the
   proof needs NO start-up hypothesis of its own: psh_rodata_chk is a vm_compute. The cells, by section of the
   asan image (a Theorem Labs lane's import check, 2026-10-29, read the section of each from the unstripped twin):
   FILE-BACKED -- the value is the image's own bytes:
     .got  0x9b700 -> 0x135328 (common_flags)  0x9b710 -> 0xa37f8   0x9b718 -> 0xa44e8
     .got  0x9b720 -> 0xa44f0                  0x9b728 -> 0xa44e0   0x9b730 -> 0x9d580
     .data 0x9d580 (__interception::real_memset) -> 0x94e40 (musl memset)    REAL(memset) (0x55e3c-0x55e48, 0x55f54)
   NOBITS (.bss) -- NOT a file fact: the value is the START-UP STATE, measured by a Theorem Labs lane in all 50 of
   scene's collected hand-off states, and it enters through the start-up certificate that supplies Tfib_const:
     0xa305c = 1                 can_poison_memory              (0x55bdc-0x55be8)
     0xa37f8 = 0x7fff8000        __asan_shadow_memory_dynamic_address, the shadow offset (0x55bf4-0x55bfc)
     0xa44e8 = 0                 kMidMemBeg                     (0x55c14-0x55c50, 0x55dfc-0x55e38)
     0xa44f0 = 0                 kMidMemEnd
     0xa44e0 = 0x7fffffffffff    kHighMemEnd
     0x1353a0 = 2^64-1           common_flags+0x78, clear_shadow_mmap_threshold (0x55e64-0x55e70)
   AR is kept by lib/Reusable/RT_PoisonFrameLaw.v (the frame may be free: free_8's case), which is why the
   post does not need the frame to be live. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AB1w AE34 AF0l AF0m AF0x AE2y AE3d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import AsStackLeaf RT_PoisonFrameLaw.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require PcapImgEnd YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition PS_ENTRY : Z := 0x551a8.
Definition PSTK : Z := 256.
Definition psh_ranges : list (Z * nat) := [(PS_ENTRY, 319%nat)].
Definition tbl_psh : ctable := Eval vm_compute in build_ranges psh_ranges TEmpty.
Lemma tbl_psh_eq : tbl_psh = build_ranges psh_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tbl_psh). Qed.
Lemma tbl_psh_ok : table_ok tfibsegs tbl_psh.
Proof. rewrite tbl_psh_eq. apply build_ranges_ok; [unfold psh_ranges; repeat constructor; cbn; discriminate | exact (table_ok_empty tfibsegs)]. Qed.

Definition psh_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
[(0xa9c9c, 1, [(0, 1%N, 1)]);
 (0xa19d0, 8, [(0, 8%N, 0xaa438)]); (0xaa438, 8, [(0, 8%N, 0x7fff8000)]);
 (0xa19d8, 8, [(0, 8%N, 0xab128)]); (0xab128, 8, [(0, 8%N, 0)]);
 (0xa19e0, 8, [(0, 8%N, 0xab130)]); (0xab130, 8, [(0, 8%N, 0)]);
 (0xa19e8, 8, [(0, 8%N, 0xab120)]); (0xab120, 8, [(0, 8%N, 0x7fffffffffff)]);
 (0xa19f0, 8, [(0, 8%N, 0xa3850)]); (0xa3850, 8, [(0, 8%N, 0x9afa8)]);
 (0xa19c0, 8, [(0, 8%N, 0x13bf68)]); (0x13bfe0, 8, [(0, 8%N, 18446744073709551615)])].
Lemma psh_rodata_chk : forall ly, rodata_chk ly psh_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- PSTK) 0 (- PSTK) 0 [].
Definition memA : smem := stkA :: map ro_region psh_rodata.
Definition P_HI : Z := 140737479966720.
Definition P_LO : Z := 2147450872.
Definition facts_ps (hi v0 : bool) : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + PSTK) kHighMemEnd 4);
 (10%nat, if hi then mkAF kHighMemBeg P_HI 3 else mkAF 4096 P_LO 3);
 (11%nat, mkAF 8 65536 3);
 (12%nat, if v0 then mkAF 0 0 0 else mkAF 1 255 0)].
Definition ss0 (hi v0 : bool) : sstate := mkSS PS_ENTRY sr_atoms memA None (mkFacts (facts_ps hi v0) [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_psh FUEL s.

Definition cnt_sv : sv :=
SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-8)) (SOff 11 0)) (SLit 3)) (SLit 1))
(SAlu ALU_SRL (SOff 10 0) (SLit 3)).
Definition end_sv : sv := SAlu ALU_ADD (SOff 10 (-8)) (SOff 11 0).
Definition a0_sv : sv := SAlu ALU_ADD (SLit SHADOW_OFF) (SAlu ALU_SRL (SOff 10 0) (SLit 3)).
Definition a2_sv : sv := SAlu ALU_ADD cnt_sv (SLit 0).
Definition THRMAX : Z := 18446744073709551615.
Definition LOWEND : Z := 2147450879.
Definition c_v0 : acond := mkAC BC_EQ (SOff 12 0) (SLit 0).
Definition c_end : acond := mkAC BC_GEU (SLit LOWEND) end_sv.
Definition c_thr : acond := mkAC BC_LTU cnt_sv (SLit THRMAX).
Definition cs1 (v0 : bool) : list acond := if v0 then [c_v0] else [].
Definition cs2 (hi : bool) : list acond := if hi then [] else [c_end].
Definition cs3 (v0 : bool) : list acond := if v0 then [c_thr] else [].
Definition ADDC (cs : list acond) (s : sstate) : sstate := fold_left add_cond cs s.
Definition S1 (hi v0 : bool) : sstate := ss0 hi v0.
Definition E1 (hi v0 : bool) : sstate := fst (RUN (S1 hi v0)).
Definition S2 (hi v0 : bool) : sstate := ADDC (cs1 v0) (E1 hi v0).
Definition E2 (hi v0 : bool) : sstate := fst (RUN (S2 hi v0)).
Definition S3 (hi v0 : bool) : sstate := ADDC (cs2 hi) (E2 hi v0).
Definition E3 (hi v0 : bool) : sstate := fst (RUN (S3 hi v0)).
Definition S4 (hi v0 : bool) : sstate := ADDC (cs3 v0) (E3 hi v0).
Definition E4 (hi v0 : bool) : sstate := fst (RUN (S4 hi v0)).

Lemma st_m1 : forall hi v0 (A : Type) (x y : A), match snd (RUN (S1 hi v0)) with RS_ecall => x | _ => y end = y.
Proof. intros [|] [|] A x y; vm_compute; reflexivity. Qed.
Lemma st_m2 : forall hi v0 (A : Type) (x y : A), match snd (RUN (S2 hi v0)) with RS_ecall => x | _ => y end = y.
Proof. intros [|] [|] A x y; vm_compute; reflexivity. Qed.
Lemma st_m3 : forall hi v0 (A : Type) (x y : A), match snd (RUN (S3 hi v0)) with RS_ecall => x | _ => y end = y.
Proof. intros [|] [|] A x y; vm_compute; reflexivity. Qed.
Lemma st_m4 : forall hi v0 (A : Type) (x y : A), match snd (RUN (S4 hi v0)) with RS_ecall => x | _ => y end = y.
Proof. intros [|] [|] A x y; vm_compute; reflexivity. Qed.

Definition keep_regs : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition psh_shape (ss : sstate) : bool :=
(ss_pc ss =? tfib_A_musl_memset) && (match ss_resv ss with None => true | _ => false end) &&
sv_eqb (sr_get (ss_regs ss) 10%bv) a0_sv && sv_eqb (sr_get (ss_regs ss) 11%bv) (SOff 12 0) &&
sv_eqb (sr_get (ss_regs ss) 12%bv) a2_sv &&
forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) keep_regs.
Lemma shape_ok : forall hi v0, psh_shape (E4 hi v0) = true.
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.

Definition win_ok (rs : smem) : bool :=
forallb (fun t => win_eqb t (Some 2%nat, - PSTK, 0) || (snd t <=? snd (fst t))) (windows rs).
Lemma wins_ok : forall hi v0,
win_ok (ss_mem (S1 hi v0)) = true /\ win_ok (ss_mem (S2 hi v0)) = true /\
win_ok (ss_mem (S3 hi v0)) = true /\ win_ok (ss_mem (S4 hi v0)) = true.
Proof. intros [|] [|]; repeat split; vm_compute; reflexivity. Qed.
Definition win0_ok (ss : sstate) : bool :=
match ss_mem ss with
| r :: _ => (match YP09.r_base r with Some k => Nat.eqb k 2 | None => false end)
            && (YP09.r_wlo r =? - PSTK) && (YP09.r_whi r =? 0)
| [] => false
end.
Lemma win0_E4 : forall hi v0, win0_ok (E4 hi v0) = true.
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.

(* The two symbolic values the tail jump hands to musl memset. *)
Lemma a0_sv_U : forall E p, bv_unsigned (ew E 10) = p -> 0 <= p < 2 ^ 47 -> U E a0_sv = shadow_addr p.
Proof.
intros E p Hp Hr. rewrite (U_zev E a0_sv) by (vm_compute; reflexivity). unfold a0_sv. cbn [zev zalu_raw].
unfold rho_of. rewrite Hp, Z.add_0_r. change (Z.land (zcanon 3) 63) with 3. change (zcanon SHADOW_OFF) with SHADOW_OFF.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound p 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small p) by lia. rewrite (zcanon_small (p / 8)) by lia. apply zcanon_small. lia.
Qed.
Lemma cnt_sv_U : forall E p n, bv_unsigned (ew E 10) = p -> bv_unsigned (ew E 11) = n ->
8 <= p -> p + n <= 2 ^ 47 -> p mod 8 = 0 -> n mod 8 = 0 -> 8 <= n -> U E cnt_sv = n / 8.
Proof.
intros E p n Hp Hn H8 Hhi Hm1 Hm2 Hn8. rewrite (U_zev E cnt_sv) by (vm_compute; reflexivity).
unfold cnt_sv. cbn [zev zalu_raw]. unfold rho_of. rewrite Hp, Hn, !Z.add_0_r.
change (Z.land (zcanon 3) 63) with 3.
rewrite (zcanon_small (p + -8)) by lia. rewrite (zcanon_small n) by lia.
rewrite (zcanon_small (p + -8 + n)) by lia. rewrite (zcanon_small p) by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd1 : 1 <= p / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hd2 : 1 <= n / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hd3 : p / 8 + n / 8 <= 2 ^ 44)
by (pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.div_mod n 8 ltac:(lia)); lia).
assert (E1 : (p + -8 + n) / 8 = p / 8 + n / 8 - 1).
{ pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
replace (p + -8 + n) with ((p / 8 + n / 8 - 1) * 8) by lia. apply Z_div_mult. lia. }
rewrite E1. rewrite (zcanon_small (p / 8 + n / 8 - 1)) by lia. rewrite (zcanon_small 1) by lia.
rewrite (zcanon_small (p / 8 + n / 8 - 1 + 1)) by lia. rewrite (zcanon_small (p / 8)) by lia.
rewrite zcanon_small by lia. lia.
Qed.
Lemma a2_sv_U : forall E p n, bv_unsigned (ew E 10) = p -> bv_unsigned (ew E 11) = n ->
8 <= p -> p + n <= 2 ^ 47 -> p mod 8 = 0 -> n mod 8 = 0 -> 8 <= n -> U E a2_sv = n / 8.
Proof.
intros E p n Hp Hn H8 Hhi Hm1 Hm2 Hn8. rewrite (U_zev E a2_sv) by (vm_compute; reflexivity).
unfold a2_sv. cbn [zev zalu_raw]. rewrite <- (U_zev E cnt_sv) by (vm_compute; reflexivity).
rewrite (cnt_sv_U E p n Hp Hn H8 Hhi Hm1 Hm2 Hn8). change (zcanon 0) with 0. rewrite Z.add_0_r.
pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound n 8 n ltac:(lia) ltac:(lia)).
apply zcanon_small. lia.
Qed.
Lemma end_sv_U : forall E p n, bv_unsigned (ew E 10) = p -> bv_unsigned (ew E 11) = n ->
8 <= p -> 8 <= n -> p + n <= 2 ^ 47 -> U E end_sv = p + n - 8.
Proof.
intros E p n Hp Hn H8 Hn8 Hhi. rewrite (U_zev E end_sv) by (vm_compute; reflexivity).
unfold end_sv. cbn [zev zalu_raw]. unfold rho_of. rewrite Hp, Hn, Z.add_0_r.
rewrite (zcanon_small (p + -8)) by lia. rewrite (zcanon_small n) by lia. rewrite zcanon_small by lia. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma psh_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> RUN ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_psh tbl_psh_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma st_ok_addc : forall E ms cs ss, st_ok tfibsegs E ss ms -> Forall (acond_ok E) cs ->
st_ok tfibsegs E (ADDC cs ss) ms.
Proof.
intros E ms cs. induction cs as [|c t IH]; intros ss HS HF; [exact HS|].
apply Forall_cons_iff in HF as [Hc HF]. unfold ADDC. cbn [fold_left].
apply IH; [|exact HF]. destruct c as [cc a b]. unfold acond_ok in Hc. cbn [ac_c ac_a ac_b] in Hc.
exact (st_ok_add_cond tfibsegs E ss ms cc a b HS Hc).
Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.
Theorem scene_poison_shadow : AsStackLeaf.poison_shadow_realizes tfibsegs B PS_ENTRY.
Proof.
intros ly S W regs mem md cid pos p n v HAR Hra Hal16 Hslo Htop HpresE Hgp Htp Hcid Hpos G10 G11 G12 Hv Hn0 Hn8 Hp8 Hfa1 Hfa2 Hpsh.
change AsStackLeaf.PS_STK with PSTK in *.
pose proof AF0x.Hwx_tfa as Hwx.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
pose proof (proj1 HAR) as M.
pose proof (am_layout B ly S _ M) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
pose proof (frame_off_bounds cid pos Hcid Hpos) as (FO1 & FO2 & FO3 & FO4 & FO5 & FO6).
destruct (F_app ly HLY) as (FH0 & FHZ & _).
set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
assert (HFA : ly_F ly + kFakeFramesOff <= fa /\ fa + fb <= ly_F ly + kFakeStackSize).
{ unfold fa, frame_addr, fb. unfold kFakeFramesOff in *. lia. }
assert (Hfb64 : 64 <= fb <= 65536).
{ unfold fb, fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia. split; [|].
- pose proof (Z.pow_le_mono_r 2 0 cid ltac:(lia) ltac:(lia)). cbn in *. lia.
- pose proof (Z.pow_le_mono_r 2 cid 10 ltac:(lia) ltac:(lia)). cbn in *. lia. }
(* the two zones the layout allows for the fake stack, and v = 0 or not *)
assert (ZONE : exists hi : bool, if hi then kHighMemBeg <= p /\ p + n <= P_HI else 4096 <= p /\ p + n <= P_LO + 8).
{ unfold kFakeFramesOff, kFakeStackSize, kLowShadowBeg, P_HI, P_LO in *.
destruct FHZ as [X | [X1 X2]]; [exists false | exists true]; cbv iota; lia. }
destruct ZONE as [hi HZ].
assert (HVB : exists v0 : bool, if v0 then v = 0 else 1 <= v <= 255)
by (destruct (Z.eq_dec v 0) as [->|Hne]; [exists true | exists false]; cbv iota; lia).
destruct HVB as [v0 HV].
assert (Hp47 : 8 <= p /\ p + n <= 2 ^ 47)
by (destruct hi; cbv iota in HZ; unfold kHighMemBeg, P_HI, P_LO in *; lia).
assert (Hn64 : 8 <= n <= 65536) by lia.
assert (Hsp : 17594333495296 + 256 <= sp0 <= 140737488355328)
by (unfold kHighMemBeg, kHighMemEnd, PSTK in *; lia).
(* the shadow range of the write, inside the frame's shadow *)
set (q := shadow_addr p) in *.
assert (Hdm : p = 8 * (p / 8) /\ n = 8 * (n / 8)).
{ pose proof (Z.div_mod p 8 ltac:(lia)) as D1. pose proof (Z.div_mod n 8 ltac:(lia)) as D2.
rewrite Hp8 in D1. rewrite Hn8 in D2. lia. }
assert (Hd8 : 0 <= p / 8 /\ 0 <= n / 8 /\ p / 8 + n / 8 <= 2 ^ 44)
by (split; [apply Z.div_pos; lia | split; [apply Z.div_pos; lia | lia]]).
assert (HQ1 : SHADOW_OFF <= q < kHighMemBeg).
{ unfold q, shadow_addr, SHADOW_OFF, kHighMemBeg in *. lia. }
assert (HQN : q + n / 8 <= kHighMemBeg).
{ unfold q. apply (shadow_range_below p n); [lia | lia | unfold kHighMemEnd; lia]. }
assert (HQFa : forall a, q <= a < q + n / 8 -> in_zr a (RT_PoisonFrameLaw.frame_shadow ly cid pos)).
{ unfold RT_PoisonFrameLaw.frame_shadow, in_zr, q, fa in *. cbn [fst snd].
assert (D1 : shadow_addr (frame_addr ly cid pos) <= shadow_addr p).
{ unfold shadow_addr. pose proof (Z.div_le_mono (frame_addr ly cid pos) p 8 ltac:(lia) ltac:(lia)). lia. }
assert (D2 : shadow_addr p + n / 8 <= shadow_addr (frame_addr ly cid pos) + fb / 8).
{ unfold shadow_addr.
pose proof (Z.div_mod (frame_addr ly cid pos) 8 ltac:(lia)) as DM1.
pose proof (Z.div_mod p 8 ltac:(lia)) as DM2. pose proof (Z.div_mod n 8 ltac:(lia)) as DM3.
pose proof (Z.div_mod fb 8 ltac:(lia)) as DM4. pose proof (Z.mod_pos_bound (frame_addr ly cid pos) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound fb 8 ltac:(lia)). lia. }
intros a Ha; lia. }
(* the environment of the walk *)
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : bv_unsigned (ew EE 10) = p) by (rewrite (EEreg 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (EE11 : bv_unsigned (ew EE 11) = n) by (rewrite (EEreg 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (EE12 : bv_unsigned (ew EE 12) = v) by (rewrite (EEreg 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (HS0 : st_ok tfibsegs EE (S1 hi v0) (restrict H (mkst regs (Z_to_bv 64 PS_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold S1, ss0, EE, AE2y.Env. apply (entry_st_ok_full tfibsegs);
change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memA. apply Forall_cons; [| exact (rodata_ok B TB psh_rodata ly S H mem _ (psh_rodata_chk ly) M)].
unfold stkA. apply (region_ok_stack tfibsegs _ _ 2 sp0 (- PSTK));
[exact EE2 | unfold PSTK in *; lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP, kHighMemBeg in *; lia|].
apply HpresE. unfold sp0, PSTK in *. lia.
- apply pairwise_disjoint_of_extents. unfold memA, stkA, psh_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold PSTK, kHighMemBeg in *.
repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms]. unfold facts_ps. destruct hi; destruct v0;
cbv iota in HZ, HV;
cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite EE2, EE10, EE11, EE12; change (2 ^ 4) with 16; change (2 ^ 3) with 8; change (2 ^ 0) with 1;
unfold kHighMemBeg, kHighMemEnd, P_HI, P_LO, PSTK in *;
repeat split; first [exact Hal16 | exact Hn8 | exact Hp8 | apply Z.mod_1_r | lia]. }
(* phase 1 *)
unfold cfg_at. change (w64 PS_ENTRY) with (Z_to_bv 64 PS_ENTRY).
eapply SRr_bind; [apply (psh_phase W EE _ _ _ _ _ HS0 ltac:(apply surjective_pairing))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _).
rewrite (st_m1 hi v0) in HS1. fold (E1 hi v0) in HS1.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (SB1 : same_but_materialized md md1) by (unfold md1; apply with_vm_backing_same).
destruct (wins_ok hi v0) as (WA & WB & WC & WD).
assert (MEQ1 : forall z : word, ~ (sp0 - PSTK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
pose proof (in_wrange_single_b EE _ (bv_unsigned z) 2%nat (- PSTK) 0 sp0 WA EE2 Hin) as X0. lia. }
clear HF1.
(* phase 2: the v = 0 test *)
assert (HC1 : Forall (acond_ok EE) (cs1 v0)).
{ unfold cs1. destruct v0; [|constructor]. cbv iota in HV. apply Forall_cons; [|constructor].
unfold acond_ok, c_v0. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U.
rewrite !(U_zev EE) by (vm_compute; reflexivity). cbn [zev]. unfold rho_of. rewrite EE12, Z.add_0_r.
rewrite !zcanon_small by lia. apply Z.eqb_eq. lia. }
assert (HS1' : st_ok tfibsegs EE (S2 hi v0) (restrict H ms1)) by (unfold S2; exact (st_ok_addc EE _ _ _ HS1 HC1)).
eapply SRr_bind; [apply (psh_phase W EE _ _ _ _ _ HS1' ltac:(apply surjective_pairing))|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & _).
rewrite (st_m2 hi v0) in HS2. fold (E2 hi v0) in HS2.
set (md2 := with_vm_backing (m_vm_lazy md1) mat2 md1) in *.
assert (SB2 : same_but_materialized md md2)
by (apply (same_but_materialized_trans md md1 md2 SB1); unfold md2; apply with_vm_backing_same).
assert (MEQ2 : forall z : word, ~ (sp0 - PSTK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite <- (MEQ1 z Hz). apply (HF2 z). intros Hin.
pose proof (in_wrange_single_b EE _ (bv_unsigned z) 2%nat (- PSTK) 0 sp0 WB EE2 Hin) as X0. lia. }
clear HF2.
(* phase 3: the low-zone end-address test *)
assert (HC2 : Forall (acond_ok EE) (cs2 hi)).
{ unfold cs2. destruct hi; [constructor|]. cbv iota in HZ. apply Forall_cons; [|constructor].
unfold acond_ok, c_end. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U.
rewrite (end_sv_U EE p n EE10 EE11 ltac:(lia) ltac:(lia) ltac:(lia)).
rewrite (U_zev EE (SLit LOWEND)) by (vm_compute; reflexivity). cbn [zev].
rewrite (zcanon_small LOWEND) by (unfold LOWEND; lia).
apply Bool.negb_true_iff. apply Z.ltb_ge. unfold LOWEND, P_LO in *. lia. }
assert (HS2' : st_ok tfibsegs EE (S3 hi v0) (restrict H ms2)) by (unfold S3; exact (st_ok_addc EE _ _ _ HS2 HC2)).
eapply SRr_bind; [apply (psh_phase W EE _ _ _ _ _ HS2' ltac:(apply surjective_pairing))|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & _).
rewrite (st_m3 hi v0) in HS3. fold (E3 hi v0) in HS3.
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2) in *.
assert (SB3 : same_but_materialized md md3)
by (apply (same_but_materialized_trans md md2 md3 SB2); unfold md3; apply with_vm_backing_same).
assert (MEQ3 : forall z : word, ~ (sp0 - PSTK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite <- (MEQ2 z Hz). apply (HF3 z). intros Hin.
pose proof (in_wrange_single_b EE _ (bv_unsigned z) 2%nat (- PSTK) 0 sp0 WC EE2 Hin) as X0. lia. }
clear HF3.
(* phase 4: the ReleaseMemoryPagesToOS threshold test *)
assert (HC3 : Forall (acond_ok EE) (cs3 v0)).
{ unfold cs3. destruct v0; [|constructor]. apply Forall_cons; [|constructor].
unfold acond_ok, c_thr. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U.
rewrite (cnt_sv_U EE p n EE10 EE11 ltac:(lia) ltac:(lia) Hp8 Hn8 ltac:(lia)).
rewrite (U_zev EE (SLit THRMAX)) by (vm_compute; reflexivity). cbn [zev].
rewrite (zcanon_small THRMAX) by (unfold THRMAX; lia).
apply Z.ltb_lt. pose proof (Z.div_le_upper_bound n 8 n ltac:(lia) ltac:(lia)). unfold THRMAX. lia. }
assert (HS3' : st_ok tfibsegs EE (S4 hi v0) (restrict H ms3)) by (unfold S4; exact (st_ok_addc EE _ _ _ HS3 HC3)).
eapply SRr_bind; [apply (psh_phase W EE _ _ _ _ _ HS3' ltac:(apply surjective_pairing))|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & _).
rewrite (st_m4 hi v0) in HS4. fold (E4 hi v0) in HS4.
set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
assert (SB4 : same_but_materialized md md4)
by (apply (same_but_materialized_trans md md3 md4 SB3); unfold md4; apply with_vm_backing_same).
assert (MEQ : forall z : word, ~ (sp0 - PSTK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite <- (MEQ3 z Hz). apply (HF4 z). intros Hin.
pose proof (in_wrange_single_b EE _ (bv_unsigned z) 2%nat (- PSTK) 0 sp0 WD EE2 Hin) as X0. lia. }
clear HF4 MEQ1 MEQ2 MEQ3.
(* the state at the tail jump into musl memset *)
pose proof (shape_ok hi v0) as Hsh. unfold psh_shape in Hsh.
apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh R12].
apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10].
apply andb_prop in Hsh as [Hpc Hrv0]. apply Z.eqb_eq in Hpc.
assert (Hrv : ss_resv (E4 hi v0) = None) by (destruct (ss_resv (E4 hi v0)); [discriminate | reflexivity]).
rewrite forallb_forall in HK.
set (regs1 := ms_regs ms4) in *. set (mem1 := ms_mem ms4) in *.
assert (RD : forall (r : bv 5) sv0, sv_eqb (sr_get (ss_regs (E4 hi v0)) r) sv0 = true -> getr regs1 r = sv_denot EE sv0).
{ intros r sv0 Hr. apply sv_eqb_eq in Hr. rewrite <- Hr. exact (st_ok_reg_denot H EE (E4 hi v0) ms4 r HS4). }
assert (KEEP1 : forall r, In r keep_regs -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. specialize (HK r Hr). cbn beta in HK. rewrite (RD (Z_to_bv 5 r) _ HK).
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply EEreg.
unfold keep_regs in Hr. cbn [In] in Hr.
assert (Hr32 : 0 <= r < 32) by (clear - Hr; lia).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
assert (Hq64 : 0 <= q < 2 ^ 64) by (unfold SHADOW_OFF, kHighMemBeg in HQ1; lia).
assert (A10 : getr regs1 10 = w64 q).
{ rewrite (RD 10%bv _ R10). apply bv_eq.
change (bv_unsigned (sv_denot EE a0_sv)) with (U EE a0_sv). rewrite (a0_sv_U EE p EE10 ltac:(lia)).
unfold w64. rewrite unsigned_lit_small by exact Hq64. reflexivity. }
assert (A11 : getr regs1 11 = w64 v).
{ rewrite (RD 11%bv _ R11). cbn [sv_denot]. rewrite EE12, Z.add_0_r. reflexivity. }
assert (A12 : getr regs1 12 = w64 (n / 8)).
{ rewrite (RD 12%bv _ R12). apply bv_eq.
change (bv_unsigned (sv_denot EE a2_sv)) with (U EE a2_sv).
rewrite (a2_sv_U EE p n EE10 EE11 ltac:(lia) ltac:(lia) Hp8 Hn8 ltac:(lia)).
unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (A1 : getr regs1 1 = getr regs 1) by (exact (KEEP1 1 ltac:(unfold keep_regs; cbn [In]; tauto))).
assert (Hcnt : 1 <= n / 8 <= 8192).
{ split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
(* presence of the shadow bytes and of the stack window after the walk *)
assert (PRS : forall a, sp0 - PSTK <= a < sp0 -> apresent H mem1 a).
{ intros a Ha. destruct (ss_mem (E4 hi v0)) as [|r0 rest] eqn:Hm0;
[pose proof (win0_E4 hi v0) as X; unfold win0_ok in X; rewrite Hm0 in X; discriminate|].
pose proof (win0_E4 hi v0) as X. unfold win0_ok in X. rewrite Hm0 in X.
apply andb_prop in X as [X Hwhi]. apply andb_prop in X as [Hb Hwlo].
apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi.
destruct (YP09.r_base r0) as [k|] eqn:Hbb; [|discriminate]. apply Nat.eqb_eq in Hb. subst k.
apply (AF0x.st_ok_window_apresent H EE (E4 hi v0) ms4 0 r0 a HS4 ltac:(rewrite Hm0; reflexivity));
[rewrite Hbb, Hwlo, Hwhi; cbn [base_val]; rewrite EE2; unfold PSTK in *; lia
| unfold AF0x.TFIB_IMG_END, PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP, kHighMemBeg in *; lia]. }
assert (PRQ : forall a, q <= a < q + n / 8 -> apresent H mem1 a).
{ intros a Ha. apply (AF0x.apresent_same H mem mem1).
- apply MEQ. rewrite unsigned_lit_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
unfold kHighMemBeg, PSTK in *. lia.
- apply Hpsh. exact Ha. }
(* musl memset *)
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS4 Hrv) as Hshape1. rewrite Hpc in Hshape1.
fold regs1 mem1 in Hshape1. rewrite Hshape1.
assert (DW : forall a, q <= a < q + n / 8 -> writable_at tfibsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (PRQ a Ha) as [Hh [b Hb]]. split; [|exact Hh].
apply AE2y.apresent_writable. split; [exact Hh|]. exists b. exact Hb. }
set (nn := Z.to_nat (n / 8)). assert (Hnn : Z.of_nat nn = n / 8) by (subst nn; lia).
assert (HQL : 2147450880 <= q /\ q + n / 8 <= 17594333495296)
by (unfold SHADOW_OFF, kHighMemBeg in HQ1, HQN; lia).
assert (SOK : store_ok tfibsegs (mrestrict H mem1) (w64 q) nn = true).
{ apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia);
[unfold SHADOW_OFF, kHighMemBeg in *; lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(lia))) as Wz. unfold writable_at in Wz.
rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
destruct (tfib_memset (w64 q) (w64 v) (w64 (n / 8)) nn (mrestrict H mem1) (seg_rom tfibsegs) regs1 A10 A11 A12
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) SOK
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia))
as (regs2 & Hms & B10 & Hkeep).
rewrite A1, Hra in Hms.
set (cb := Z_to_bv 8 (bv_unsigned (w64 v) mod 256)) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 q) (repeat cb nn)) in Hms.
set (mem2 := munrestrict H mem1 m2r).
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _.
pose proof (same_but_materialized_trans md md4 model' SB4 Hsbm) as HSBM.
change (unrestrict H mem1 (mkst regs2 (getr regs 1) m2r (seg_rom tfibsegs))) with (mkst regs2 (getr regs 1) mem2 (seg_rom tfibsegs)).
assert (LEN : Z.of_nat (length (repeat cb nn)) = n / 8) by (rewrite repeat_length; exact Hnn).
assert (M2out : forall z : word, ~ (q <= bv_unsigned z < q + n / 8) -> mem2 z = mem1 z).
{ intros z Hz. subst mem2 m2r. unfold munrestrict. destruct (H z) eqn:Hh; [reflexivity|].
assert (Ew : wbytes m1r (w64 q) (repeat cb nn) z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) q) as [L|L].
- apply wbytes_below; unfold w64; rewrite ?LEN, unsigned_lit_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia); lia.
- apply wbytes_above. unfold w64. rewrite LEN, unsigned_lit_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia). lia. }
rewrite Ew. subst m1r. unfold mrestrict. rewrite Hh. reflexivity. }
assert (M2in : forall i, 0 <= i < n / 8 -> mem2 (Z_to_bv 64 (q + i)) = Some cb).
{ intros i Hi. subst mem2. unfold munrestrict. rewrite (proj2 (DW (q + i) ltac:(lia))).
subst m2r. rewrite (AE2y.wbytes_inside (repeat cb nn) m1r (w64 q) (Z_to_bv 64 (q + i)));
unfold w64; rewrite ?LEN, ?unsigned_lit_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia);
[|unfold SHADOW_OFF, kHighMemBeg in *; lia|unfold SHADOW_OFF, kHighMemBeg in *; lia].
replace (Z.to_nat (q + i - q)) with (Z.to_nat i) by lia. apply nth_error_repeat. lia. }
assert (CB : bv_unsigned cb = v).
{ subst cb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold w64.
rewrite unsigned_lit_small by lia. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (AVin : forall i, 0 <= i < n / 8 -> aview tfibsegs H mem2 (q + i) = Some v).
{ intros i Hi. unfold aview, mbyte, mrestrict. rewrite (proj2 (DW (q + i) ltac:(lia))), (M2in i Hi).
cbn [option_map]. rewrite CB. reflexivity. }
assert (AVout : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n / 8) -> ~ (sp0 - PSTK <= a < sp0) ->
aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr Ha Hs. apply aview_same. rewrite (M2out (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Ha)).
apply MEQ. rewrite unsigned_lit_small by lia. exact Hs. }
assert (PRE2 : forall a, sp0 - PSTK <= a < sp0 -> apresent H mem2 a).
{ intros a Ha. apply (AF0x.apresent_same H mem1 mem2); [|apply PRS; exact Ha].
apply M2out. rewrite unsigned_lit_small by (unfold kHighMemBeg, kHighMemEnd, PSTK in *; lia).
unfold kHighMemBeg, PSTK in *. lia. }
apply SRr_ret. split; [reflexivity|]. exists regs2, mem2, model'.
pose proof (same_but_materialized_frame md model' HSBM) as MF.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [|split; [|split; [exact HSBM | split; [exact AVin | split; [exact AVout | exact PRE2]]]]].
-
apply (RT_PoisonFrameLaw.AR_poison_frame tfibsegs B ly S W mem md mem2 model' cid pos HAR Hcid Hpos).
+ intros a Hr Hown Hns. apply AVout; [exact Hr| |].
* intros Hin. exact (Hns (HQFa a Hin)).
* intros Hin. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0, PSTK in *; lia) Hown).
+ intros a Hva. rewrite (AE2y.aview_mod _ mem2 a). rewrite (AE2y.aview_mod _ mem a) in Hva.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' q) as [L1|L1]; [|destruct (Z_lt_le_dec a' (q + n / 8)) as [L2|L2]].
* destruct (Z_lt_le_dec a' (sp0 - PSTK)) as [L3|L3]; [rewrite AVout by lia; exact Hva|].
destruct (Z_lt_le_dec a' sp0) as [L4|L4]; [apply AE2y.aview_some_of_apresent; apply PRE2; lia
| rewrite AVout by lia; exact Hva].
* replace a' with (q + (a' - q)) by lia. rewrite AVin by lia. discriminate.
* destruct (Z_lt_le_dec a' (sp0 - PSTK)) as [L3|L3]; [rewrite AVout by lia; exact Hva|].
destruct (Z_lt_le_dec a' sp0) as [L4|L4]; [apply AE2y.aview_some_of_apresent; apply PRE2; lia
| rewrite AVout by lia; exact Hva].
+ apply MF. + apply MF. + apply MF.
+ intros a Hb Hh. change (w_H W (w64 a)) with (H (Z_to_bv 64 a)) in Hh.
assert (Hr : 0 <= a < 2 ^ 64) by (exact (AE2y.in_band_rw_u64 a Hb)).
change (mem2 (w64 a) = mem (w64 a)) with (mem2 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
rewrite (M2out (Z_to_bv 64 a)); [| rewrite unsigned_lit_small by lia; intros Hin;
rewrite (proj2 (DW a Hin)) in Hh; discriminate].
apply MEQ. rewrite unsigned_lit_small by lia. intros Hin.
destruct (HpresE a Hin) as [Hh0 _]. rewrite Hh0 in Hh. discriminate.
-
intros r Hr.
assert (NE : forall x : bv 5, 11 <= bv_unsigned x <= 16 -> Z_to_bv 5 r <> x).
{ intros x Hx E. rewrite <- E in Hx. rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap in Hx.
change (bv_modulus 5) with 32 in Hx. unfold acallee_saved in Hr. rewrite Z.mod_small in Hx by lia. lia. }
rewrite Hkeep; [apply KEEP1; unfold acallee_saved in Hr; unfold keep_regs; cbn [In]; lia | | | | | |];
apply NE; (split; apply Z.leb_le; reflexivity).
Qed.
End d.
End c.
