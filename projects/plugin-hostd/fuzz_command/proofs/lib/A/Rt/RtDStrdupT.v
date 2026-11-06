(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> CmdBSyms, its addresses moved to plugin-hostd/fuzz_command's ASan build, and the module destructor's write set XW2 stated with the shadow of the whole image ([0x7fffa000, 0x800b8c00)) instead of the shadow bytes of cgif's three registered globals (fuzz_command registers 180), plus the odr indicator bytes of the four globals that have one (0x5e3c40..0x5e3c42, 0x5e3c80), which __asan_unregister_globals clears. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/AE23.v, with its module names changed; 296 of its 330 lines of code are new or changed and 1641 lines of the source are left out. *)
(* The tail of plugin-hostd/fuzz_command's strdup entry (___interceptor_strdup 0x4ccb0), from the instruction right
   after its call of __asan::asan_malloc to its return, measured on the pinned fuzz_command.asan:
     0x4ce9c bnez a0,0x4ce20          0x4cea0 j 0x4ce40
     0x4ce20 auipc a1,0x59; ld a1,1528(a1) (= [0xa6418] = 0xa82a8); ld a3,0(a1) (= [0xa82a8] = 0x9eb3c, musl memcpy)
     0x4ce2c mv s3,a0; mv a1,s1; mv a2,s2; 0x4ce38 jalr a3 (memcpy(a0 = the block, a1 = the source, a2 = the count))
     0x4ce3c mv a0,s3
     0x4ce40 addi sp,sp,112; the nine saved words ra s0 s1 s2 s3 s4 s5 s6 s7 come back from sp0-8 .. sp0-72;
     0x4ce68 addi sp,sp,2032; 0x4ce6c ret
   The walk seeds a symbolic state at 0x4ce9c whose stack region holds only the nine saved words (offsets 2072..2144
   above the current sp, atoms 32..40) and whose two read-only regions hold the memcpy pointer pair. Every region is
   read-only, so each run leaves the memory as it was. musl memcpy is crossed with AE3c.tfib_memcpy; the
   stack region is kept over it because the copied range lies outside the nine saved words. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDStrdupD.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE3c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The memcpy pointer pair the tail loads: [0xa6418] = 0xa82a8 and [0xa82a8] = 0x9eb3c. *)
Definition sdt_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
[ (0xa6418, 8, [(0, 8%N, 0xa82a8)]); (0xa82a8, 8, [(0, 8%N, 0x9eb3c)]) ].
(* The nine saved words, at sp0-8 .. sp0-72, i.e. 2136 .. 2072 above the sp of the tail (sp0 - 2144). *)
Definition sdt_chunks : list YP09.chunk :=
[YP09.mkChunk 2136 (CVal 8 (SOff 32 0)); YP09.mkChunk 2128 (CVal 8 (SOff 33 0));
YP09.mkChunk 2120 (CVal 8 (SOff 34 0)); YP09.mkChunk 2112 (CVal 8 (SOff 35 0));
YP09.mkChunk 2104 (CVal 8 (SOff 36 0)); YP09.mkChunk 2096 (CVal 8 (SOff 37 0));
YP09.mkChunk 2088 (CVal 8 (SOff 38 0)); YP09.mkChunk 2080 (CVal 8 (SOff 39 0));
YP09.mkChunk 2072 (CVal 8 (SOff 40 0))].
Definition sdt_stk : YP09.region := YP09.mkRegion (Some 2%nat) 2072 2144 2144 2144 sdt_chunks.
Definition sdt_ss : sstate :=
mkSS 0x4ce9c sr_atoms (sdt_stk :: map ro_region sdt_rodata) None (mkFacts [(2%nat, mkAF (2 ^ 43) (2 ^ 47) 4)] [] []).

(* After a run over read-only regions the memory is the one before it. *)
Ltac sdt_ro HF HFr M :=
lazymatch type of HF with frame_of _ ?rs ?m0 ?m1 =>
pose proof (frame_of_read_only _ rs m0 m1 ltac:(vm_compute; reflexivity) HF) as M; clear HF HFr
end.
(* The model term of a run, named, so that it does not grow over a chain of runs. *)
Ltac sdt_md HMD :=
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m) ?X ?m] =>
let mdv := fresh "mdv" in let Hs := fresh "HMDs" in
pose proof (same_but_materialized_trans _ _ _ HMD (with_vm_backing_same m X)) as Hs;
set (mdv := with_vm_backing (m_vm_lazy m) X m) in *; clearbody mdv; clear HMD; rename Hs into HMD
end.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* musl memcpy's frame clause keeps every callee-saved register. *)
Lemma sdt_rp : forall regs regs' : bvmap 5 word,
(forall r : bv 5, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv ->
r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv ->
getr regs' r = getr regs r) ->
regs_preserved regs regs'.
Proof.
intros regs regs' K r Hr. unfold callee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [Hc|Hc]; [subst r; apply K; intros Heq; apply (f_equal bv_unsigned) in Heq; vm_compute in Heq; discriminate|]).
subst r; apply K; intros Heq; apply (f_equal bv_unsigned) in Heq; vm_compute in Heq; discriminate.
Qed.

Lemma bv5_24_27 : forall r : bv 5, 24 <= bv_unsigned r <= 27 -> r = 24%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv.
Proof.
intros r Hr.
assert (H : bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
destruct H as [H|[H|[H|H]]]; [left | right; left | right; right; left | right; right; right];
apply bv_eq; rewrite H; reflexivity.
Qed.

(* A callee given as [msteps] over the restricted memory, which writes that memory. *)
Lemma sdt_msteps_w : forall (W : world tfibsegs) regs0 pc0 (mem0 : word -> option byte) md0 regs1 pc1
(m1 : word -> option byte) Q,
msteps tfibsegs (mkst regs0 pc0 (mrestrict (w_H W) mem0) (seg_rom tfibsegs)) (mkst regs1 pc1 m1 (seg_rom tfibsegs)) ->
(forall md1, same_but_materialized md0 md1 ->
restrict (w_H W) (mkst regs1 pc1 (munrestrict (w_H W) mem0 m1) (seg_rom tfibsegs)) = mkst regs1 pc1 m1 (seg_rom tfibsegs) ->
SRr tfibsegs W (mkCfg (mkst regs1 pc1 (munrestrict (w_H W) mem0 m1) (seg_rom tfibsegs)) md1) Q) ->
SRr tfibsegs W (mkCfg (mkst regs0 pc0 mem0 (seg_rom tfibsegs)) md0) Q.
Proof.
intros W regs0 pc0 mem0 md0 regs1 pc1 m1 Q Hms HK.
eapply (SRr_msteps tfibsegs AF0x.Hwx_tfa W); [rewrite restrict_mkst_fx; exact Hms|].
intros md1 Hs Hcl. apply (HK md1 Hs).
exact (restrict_unrestrict_clean (w_H W) mem0 (mkst regs1 pc1 m1 (seg_rom tfibsegs)) Hcl).
Qed.

(* The return: the post of the tail from the registers the epilogue leaves. *)
Lemma sdt_close : forall (W : world tfibsegs) (regs regs' : bvmap 5 word) (M M' : word -> option byte) (md md' : Model)
(sp0 v r1 r8 r9 r18 r19 r20 r21 r22 r23 : Z),
M' = M -> 0 <= r1 < 2 ^ 64 -> r1 mod 2 = 0 ->
same_but_materialized md md' ->
getr regs' 10 = w64 v -> getr regs' 2 = w64 sp0 ->
getr regs' 1 = w64 r1 -> getr regs' 8 = w64 r8 -> getr regs' 9 = w64 r9 ->
getr regs' 18 = w64 r18 -> getr regs' 19 = w64 r19 -> getr regs' 20 = w64 r20 ->
getr regs' 21 = w64 r21 -> getr regs' 22 = w64 r22 -> getr regs' 23 = w64 r23 ->
getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
(forall r : bv 5, 24 <= bv_unsigned r <= 27 -> getr regs' r = getr regs r) ->
W = W /\ exists regs'' md'',
mkCfg (mkst regs' (v_jalr (getr regs' 1) 0) M' (seg_rom tfibsegs)) md' = cfg_at tfibsegs r1 regs'' M md'' /\
same_but_materialized md md'' /\
getr regs'' 10 = w64 v /\ getr regs'' 2 = w64 sp0 /\
getr regs'' 1 = w64 r1 /\ getr regs'' 8 = w64 r8 /\ getr regs'' 9 = w64 r9 /\
getr regs'' 18 = w64 r18 /\ getr regs'' 19 = w64 r19 /\ getr regs'' 20 = w64 r20 /\
getr regs'' 21 = w64 r21 /\ getr regs'' 22 = w64 r22 /\ getr regs'' 23 = w64 r23 /\
getr regs'' 3 = getr regs 3 /\ getr regs'' 4 = getr regs 4 /\
(forall r : bv 5, 24 <= bv_unsigned r <= 27 -> getr regs'' r = getr regs r).
Proof.
intros W regs regs' M M' md md' sp0 v r1 r8 r9 r18 r19 r20 r21 r22 r23 HM Hr1 Hr1e Hsbm
F10 F2 F1 F8 F9 F18 F19 F20 F21 F22 F23 F3 F4 F24.
split; [reflexivity|]. exists regs', md'.
split.
{ unfold cfg_at. rewrite HM, F1.
assert (RO : ret_ok (w64 r1)) by (apply ret_ok_even; unfold w64; rewrite unsigned_lit_small by lia; exact Hr1e).
unfold ret_ok in RO. rewrite RO. reflexivity. }
split; [exact Hsbm|]. split; [exact F10|]. split; [exact F2|]. split; [exact F1|]. split; [exact F8|].
split; [exact F9|]. split; [exact F18|]. split; [exact F19|]. split; [exact F20|]. split; [exact F21|].
split; [exact F22|]. split; [exact F23|]. split; [exact F3|]. split; [exact F4|]. exact F24.
Qed.

Theorem sd_tail_srr :
forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(sp0 v xs n : Z) (out : list byte) (r1 r8 r9 r18 r19 r20 r21 r22 r23 : Z),
2 ^ 44 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
getr regs 2 = w64 (sp0 - 2144) -> getr regs 9 = w64 xs -> getr regs 18 = w64 n ->
getr regs 10 = w64 v ->
0 <= v < 2 ^ 64 -> 0 < n < 2 ^ 32 -> 0 <= xs -> xs + n <= 2 ^ 63 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 8) 8 r1 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 16) 8 r8 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 24) 8 r9 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 32) 8 r18 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 40) 8 r19 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 48) 8 r20 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 56) 8 r21 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 64) 8 r22 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 72) 8 r23 ->
0 <= r1 < 2 ^ 64 -> r1 mod 2 = 0 -> 4096 <= r1 ->
0 <= r8 < 2 ^ 64 -> 0 <= r9 < 2 ^ 64 -> 0 <= r18 < 2 ^ 64 -> 0 <= r19 < 2 ^ 64 ->
0 <= r20 < 2 ^ 64 -> 0 <= r21 < 2 ^ 64 -> 0 <= r22 < 2 ^ 64 -> 0 <= r23 < 2 ^ 64 ->
(forall a, sp0 - 2304 <= a < sp0 -> apresent (w_H W) mem a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0xa6418 8 0xa82a8 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0xa82a8 8 0x9eb3c ->
(v <> 0 -> length out = Z.to_nat n) ->
(v <> 0 -> rdn tfibsegs (mrestrict (w_H W) mem) (Z_to_bv 64 xs) (Z.to_nat n) = Some out) ->
(v <> 0 -> store_ok tfibsegs (mrestrict (w_H W) mem) (Z_to_bv 64 v) (Z.to_nat n) = true) ->
(v <> 0 -> v + n <= xs \/ xs + n <= v) ->
(v <> 0 -> 0 < v /\ v + n <= 2 ^ 63) ->
(v <> 0 -> v + n <= sp0 - 72 \/ sp0 <= v) ->
SRr tfibsegs W (cfg_at tfibsegs 0x4ce9c regs mem md)
(fun W' c' => W' = W /\ exists regs' md',
c' = cfg_at tfibsegs r1 regs'
(if v =? 0 then mem else munrestrict (w_H W) mem (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 v) out)) md' /\
same_but_materialized md md' /\
getr regs' 10 = w64 v /\ getr regs' 2 = w64 sp0 /\
getr regs' 1 = w64 r1 /\ getr regs' 8 = w64 r8 /\ getr regs' 9 = w64 r9 /\
getr regs' 18 = w64 r18 /\ getr regs' 19 = w64 r19 /\ getr regs' 20 = w64 r20 /\
getr regs' 21 = w64 r21 /\ getr regs' 22 = w64 r22 /\ getr regs' 23 = w64 r23 /\
getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
(forall r : bv 5, 24 <= bv_unsigned r <= 27 -> getr regs' r = getr regs r)).
Proof.
intros W regs mem md sp0 v xs n out r1 r8 r9 r18 r19 r20 r21 r22 r23 Hsp Hal G2 G9 G18 G10 Hv Hn Hxs Hxsn
V1 V8 V9 V18 V19 V20 V21 V22 V23 R1 R1e R1lo R8 R9 R18 R19 R20 R21 R22 R23 Hpres Va Vb
Hlen Hrdn Hst Hdisj Hvr Hvstk.
pose proof AF0x.Hwx_tfa as Hwx.
set (EE := AE2y.Env regs [r1; r8; r9; r18; r19; r20; r21; r22; r23]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r)
by (intros i r Hi; apply AE2y.Env_reg; exact Hi).
assert (EEx : forall j z, nth_error [r1; r8; r9; r18; r19; r20; r21; r22; r23] j = Some z -> ew EE (32 + j) = Z_to_bv 64 z)
by (intros j z Hj; exact (AE2y.Env_x regs _ j z Hj)).
assert (E2 : bv_unsigned (ew EE 2) = sp0 - 2144)
by (rewrite (EEreg 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
assert (E10 : ew EE 10 = Z_to_bv 64 v) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (E9 : ew EE 9 = Z_to_bv 64 xs) by (rewrite (EEreg 9%nat 9%bv eq_refl); exact G9).
assert (E18 : ew EE 18 = Z_to_bv 64 n) by (rewrite (EEreg 18%nat 18%bv eq_refl); exact G18).
assert (X32 : ew EE 32 = Z_to_bv 64 r1) by exact (EEx 0%nat r1 eq_refl).
assert (X33 : ew EE 33 = Z_to_bv 64 r8) by exact (EEx 1%nat r8 eq_refl).
assert (X34 : ew EE 34 = Z_to_bv 64 r9) by exact (EEx 2%nat r9 eq_refl).
assert (X35 : ew EE 35 = Z_to_bv 64 r18) by exact (EEx 3%nat r18 eq_refl).
assert (X36 : ew EE 36 = Z_to_bv 64 r19) by exact (EEx 4%nat r19 eq_refl).
assert (X37 : ew EE 37 = Z_to_bv 64 r20) by exact (EEx 5%nat r20 eq_refl).
assert (X38 : ew EE 38 = Z_to_bv 64 r21) by exact (EEx 6%nat r21 eq_refl).
assert (X39 : ew EE 39 = Z_to_bv 64 r22) by exact (EEx 7%nat r22 eq_refl).
assert (X40 : ew EE 40 = Z_to_bv 64 r23) by exact (EEx 8%nat r23 eq_refl).
(* the saved words as chunks of the stack region *)
assert (CK : forall (j : nat) off z a, nth_error [r1; r8; r9; r18; r19; r20; r21; r22; r23] j = Some z ->
off = 2136 - 8 * Z.of_nat j -> a = sp0 - 8 - 8 * Z.of_nat j -> 0 <= z < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) a 8 z ->
YP09.chunk_ok tfibsegs EE (mrestrict (w_H W) mem) (sp0 - 2144) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off z a Hj Hoff Ha Hz Hvm.
apply (chunk_ok_val tfibsegs EE _ (sp0 - 2144) off 8 _ z).
- cbn [sv_denot]. rewrite (EEx j z Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- zside.
- zside.
- replace (sp0 - 2144 + off) with a by lia. exact Hvm. }
assert (HS0 : st_ok tfibsegs EE sdt_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x4ce9c) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold sdt_ss, sdt_rodata. cbn [map].
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs);
change (Ereg regs (map (Z_to_bv 64) [r1; r8; r9; r18; r19; r20; r21; r22; r23])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ unfold region_ok, sdt_stk.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold sdt_chunks. repeat apply Forall_cons; try apply Forall_nil.
* apply (CK 0%nat 2136 r1 (sp0 - 8)); [reflexivity | reflexivity | lia | exact R1 | exact V1].
* apply (CK 1%nat 2128 r8 (sp0 - 16)); [reflexivity | reflexivity | lia | exact R8 | exact V8].
* apply (CK 2%nat 2120 r9 (sp0 - 24)); [reflexivity | reflexivity | lia | exact R9 | exact V9].
* apply (CK 3%nat 2112 r18 (sp0 - 32)); [reflexivity | reflexivity | lia | exact R18 | exact V18].
* apply (CK 4%nat 2104 r19 (sp0 - 40)); [reflexivity | reflexivity | lia | exact R19 | exact V19].
* apply (CK 5%nat 2096 r20 (sp0 - 48)); [reflexivity | reflexivity | lia | exact R20 | exact V20].
* apply (CK 6%nat 2088 r21 (sp0 - 56)); [reflexivity | reflexivity | lia | exact R21 | exact V21].
* apply (CK 7%nat 2080 r22 (sp0 - 64)); [reflexivity | reflexivity | lia | exact R22 | exact V22].
* apply (CK 8%nat 2072 r23 (sp0 - 72)); [reflexivity | reflexivity | lia | exact R23 | exact V23].
+ unfold region_ok, ro_region, ro_chunk.
cbn [fst snd map YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val tfibsegs EE _ 0 (0xa6418 + 0) 8 (SLit 0xa82a8) 0xa82a8); [reflexivity | zside | zside | exact Va].
+ unfold region_ok, ro_region, ro_chunk.
cbn [fst snd map YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val tfibsegs EE _ 0 (0xa82a8 + 0) 8 (SLit 0x9eb3c) 0x9eb3c); [reflexivity | zside | zside | exact Vb].
- apply pairwise_disjoint_of_extents. unfold sdt_stk, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
split; [lia|]. split; [|lia]. change (2 ^ 4) with 16.
replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
unfold cfg_at. change (w64 0x4ce9c) with (Z_to_bv 64 0x4ce9c).
pose proof (same_but_materialized_refl md) as HMD.
srr_branch_with tbl_sd_ok HS0.
- (* a0 <> 0: the copy, then the epilogue *)
assert (Hv0 : v <> 0).
{ rewrite branch_ne_U, (U_atom EE 10 v E10), U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
clear Hc.
destruct (Hvr Hv0) as [Hv1 Hvn].
assert (LEN : Z.of_nat (length out) = n) by (rewrite (Hlen Hv0); apply Z2Nat.id; lia).
srr_run_to_with tbl_sd_ok HS0 0x9eb3c. sdt_ro HF HFr MEQ. sdt_md HMD.
lazymatch type of HS0 with st_ok _ _ _ (restrict _ ?m) => rename m into msA end.
rreg HS0 (1%bv : bv 5) A1. rreg HS0 (10%bv : bv 5) A10. rreg HS0 (11%bv : bv 5) A11. rreg HS0 (12%bv : bv 5) A12.
assert (P10 : getr (ms_regs msA) 10 = Z_to_bv 64 v) by (rewrite A10; exact E10).
assert (P11 : getr (ms_regs msA) 11 = Z_to_bv 64 xs) by (rewrite A11; exact E9).
assert (P12 : getr (ms_regs msA) 12 = Z_to_bv 64 n) by (rewrite A12; exact E18).
assert (Pn : bv_unsigned (Z_to_bv 64 n) = Z.of_nat (length out)) by (rewrite unsigned_lit_small by lia; lia).
assert (Prd : rdn tfibsegs (mrestrict (w_H W) (ms_mem msA)) (Z_to_bv 64 xs) (length out) = Some out)
by (rewrite MEQ, (Hlen Hv0); exact (Hrdn Hv0)).
assert (Pst : store_ok tfibsegs (mrestrict (w_H W) (ms_mem msA)) (Z_to_bv 64 v) (length out) = true)
by (rewrite MEQ, (Hlen Hv0); exact (Hst Hv0)).
assert (Pd : bv_unsigned (Z_to_bv 64 v) + Z.of_nat (length out) <= 2 ^ 64) by (rewrite unsigned_lit_small by lia; lia).
assert (Ps : bv_unsigned (Z_to_bv 64 xs) + Z.of_nat (length out) <= 2 ^ 64) by (rewrite unsigned_lit_small by lia; lia).
assert (Pdj : bv_unsigned (Z_to_bv 64 v) + Z.of_nat (length out) <= bv_unsigned (Z_to_bv 64 xs)
\/ bv_unsigned (Z_to_bv 64 xs) + Z.of_nat (length out) <= bv_unsigned (Z_to_bv 64 v))
by (rewrite !unsigned_lit_small by lia; rewrite LEN; exact (Hdisj Hv0)).
destruct (AE3c.tfib_memcpy out (Z_to_bv 64 v) (Z_to_bv 64 xs) (Z_to_bv 64 n) (mrestrict (w_H W) (ms_mem msA))
(seg_rom tfibsegs) (ms_regs msA) P10 P11 P12 Pn Prd Pst Pd Ps Pdj) as (regs2 & Hms & B10 & KEEP).
rewrite A1 in Hms.
replace (v_jalr (Z_to_bv 64 0x4ce3c) 0) with (Z_to_bv 64 0x4ce3c : word) in Hms by (apply bv_eq; vm_compute; reflexivity).
change (Z_to_bv 64 tfib_A_musl_memcpy) with (Z_to_bv 64 0x9eb3c) in Hms.
assert (RP : regs_preserved (ms_regs msA) regs2) by (apply sdt_rp; exact KEEP).
assert (KEPT : Forall (region_kept tfibsegs EE (mrestrict (w_H W) (ms_mem msA))
(wbytes (mrestrict (w_H W) (ms_mem msA)) (Z_to_bv 64 v) out)) [sdt_stk]).
{ apply Forall_cons; [|apply Forall_nil].
apply (region_kept_outside tfibsegs EE _ _ sdt_stk v n).
- intros x [Hx|Hx].
+ apply wbytes_below; rewrite unsigned_lit_small by lia; [lia | exact Hx].
+ apply wbytes_above. rewrite unsigned_lit_small by lia. lia.
- apply wbytes_grows.
- unfold sdt_stk. cbn [YP09.r_base YP09.r_lo base_val]. rewrite E2. lia.
- unfold sdt_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2. pose proof (Hvstk Hv0). lia.
- unfold sdt_stk. cbn [YP09.r_base YP09.r_hi base_val]. rewrite E2. lia.
- unfold sdt_stk. cbn [YP09.r_lo YP09.r_wlo]. lia.
- unfold sdt_stk. cbn [YP09.r_whi YP09.r_hi]. lia. }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EE _ _ HS0 eq_refl) as Hshape.
lazymatch type of HS0 with st_ok _ _ ?s _ =>
assert (SUB : submem [sdt_stk] (ss_mem s)) by (apply submem_keep; [apply subregion_refl | apply submem_nil]);
assert (HRA : sr_get (ss_regs s) 1 = SLit 0x4ce3c) by (vm_compute; reflexivity);
assert (HAT : ss_atoms_lt 41 s = true) by (vm_compute; reflexivity);
assert (HWF : regions_wf [sdt_stk] = true) by (vm_compute; reflexivity);
assert (HNC : no_cdata [sdt_stk] = true) by (vm_compute; reflexivity);
assert (HMA : mem_atoms_lt 41 [sdt_stk] = true) by (vm_compute; reflexivity);
pose proof (st_ok_after_call tfibsegs 41 EE s (restrict (w_H W) msA) regs2
(wbytes (mrestrict (w_H W) (ms_mem msA)) (Z_to_bv 64 v) out) [sdt_stk] 0x4ce3c
HS0 eq_refl HAT HWF HNC HMA SUB HRA RP KEPT) as HS2
end.
clear HS0. rewrite Hshape. cbn [ss_pc].
apply (sdt_msteps_w W (ms_regs msA) (Z_to_bv 64 0x9eb3c) (ms_mem msA) _ regs2 (Z_to_bv 64 0x4ce3c) _ _ Hms).
intros md1 Hs1 Hrr.
pose proof (same_but_materialized_trans _ _ _ HMD Hs1) as HMD1. clear HMD Hs1. rename HMD1 into HMD.
rewrite <- Hrr in HS2. clear Hrr.
srr_run_to_with tbl_sd_ok HS2 0x4ce6c. sdt_ro HF HFr MEF. sdt_md HMD.
eapply (SRr_ret_at tfibsegs tbl_sd tbl_sd_ok Hwx W); [exact HS2 | reflexivity | vm_compute; reflexivity |].
intros mat'. cbv beta.
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?m) => rename m into msF end.
rreg HS2 (1%bv : bv 5) Q1. rreg HS2 (2%bv : bv 5) Q2. rreg HS2 (3%bv : bv 5) Q3. rreg HS2 (4%bv : bv 5) Q4.
rreg HS2 (8%bv : bv 5) Q8. rreg HS2 (9%bv : bv 5) Q9. rreg HS2 (10%bv : bv 5) Q10.
rreg HS2 (18%bv : bv 5) Q18. rreg HS2 (19%bv : bv 5) Q19. rreg HS2 (20%bv : bv 5) Q20.
rreg HS2 (21%bv : bv 5) Q21. rreg HS2 (22%bv : bv 5) Q22. rreg HS2 (23%bv : bv 5) Q23.
rreg HS2 (24%bv : bv 5) Q24. rreg HS2 (25%bv : bv 5) Q25. rreg HS2 (26%bv : bv 5) Q26. rreg HS2 (27%bv : bv 5) Q27.
assert (FM : ms_mem msF = (if v =? 0 then mem else munrestrict (w_H W) mem (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 v) out))).
{ rewrite MEF, MEQ. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hv0). reflexivity. }
assert (F24 : forall r : bv 5, 24 <= bv_unsigned r <= 27 -> getr (ms_regs msF) r = getr regs r).
{ intros r Hr. destruct (bv5_24_27 r Hr) as [ -> | [ -> | [ -> | -> ] ] ];
[rewrite Q24 | rewrite Q25 | rewrite Q26 | rewrite Q27]; apply EEreg; reflexivity. }
exact (sdt_close W regs (ms_regs msF) _ (ms_mem msF) md _ sp0 v r1 r8 r9 r18 r19 r20 r21 r22 r23 FM R1 R1e
(same_but_materialized_trans _ _ _ HMD (with_vm_backing_same _ mat'))
ltac:(rewrite Q10; exact E10)
ltac:(rewrite Q2, E2; unfold w64; f_equal; lia)
ltac:(rewrite Q1; exact X32) ltac:(rewrite Q8; exact X33) ltac:(rewrite Q9; exact X34)
ltac:(rewrite Q18; exact X35) ltac:(rewrite Q19; exact X36) ltac:(rewrite Q20; exact X37)
ltac:(rewrite Q21; exact X38) ltac:(rewrite Q22; exact X39) ltac:(rewrite Q23; exact X40)
ltac:(rewrite Q3; apply EEreg; reflexivity) ltac:(rewrite Q4; apply EEreg; reflexivity) F24).
- (* a0 = 0: straight to the epilogue *)
assert (Hv0 : v = 0).
{ rewrite branch_ne_U, (U_atom EE 10 v E10), U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
clear Hc.
srr_run_to_with tbl_sd_ok HS0 0x4ce6c. sdt_ro HF HFr MEF. sdt_md HMD.
eapply (SRr_ret_at tfibsegs tbl_sd tbl_sd_ok Hwx W); [exact HS0 | reflexivity | vm_compute; reflexivity |].
intros mat'. cbv beta.
lazymatch type of HS0 with st_ok _ _ _ (restrict _ ?m) => rename m into msF end.
rreg HS0 (1%bv : bv 5) Q1. rreg HS0 (2%bv : bv 5) Q2. rreg HS0 (3%bv : bv 5) Q3. rreg HS0 (4%bv : bv 5) Q4.
rreg HS0 (8%bv : bv 5) Q8. rreg HS0 (9%bv : bv 5) Q9. rreg HS0 (10%bv : bv 5) Q10.
rreg HS0 (18%bv : bv 5) Q18. rreg HS0 (19%bv : bv 5) Q19. rreg HS0 (20%bv : bv 5) Q20.
rreg HS0 (21%bv : bv 5) Q21. rreg HS0 (22%bv : bv 5) Q22. rreg HS0 (23%bv : bv 5) Q23.
rreg HS0 (24%bv : bv 5) Q24. rreg HS0 (25%bv : bv 5) Q25. rreg HS0 (26%bv : bv 5) Q26. rreg HS0 (27%bv : bv 5) Q27.
assert (FM : ms_mem msF = (if v =? 0 then mem else munrestrict (w_H W) mem (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 v) out))).
{ rewrite MEF. replace (v =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hv0). reflexivity. }
assert (F24 : forall r : bv 5, 24 <= bv_unsigned r <= 27 -> getr (ms_regs msF) r = getr regs r).
{ intros r Hr. destruct (bv5_24_27 r Hr) as [ -> | [ -> | [ -> | -> ] ] ];
[rewrite Q24 | rewrite Q25 | rewrite Q26 | rewrite Q27]; apply EEreg; reflexivity. }
exact (sdt_close W regs (ms_regs msF) _ (ms_mem msF) md _ sp0 v r1 r8 r9 r18 r19 r20 r21 r22 r23 FM R1 R1e
(same_but_materialized_trans _ _ _ HMD (with_vm_backing_same _ mat'))
ltac:(rewrite Q10; exact E10)
ltac:(rewrite Q2, E2; unfold w64; f_equal; lia)
ltac:(rewrite Q1; exact X32) ltac:(rewrite Q8; exact X33) ltac:(rewrite Q9; exact X34)
ltac:(rewrite Q18; exact X35) ltac:(rewrite Q19; exact X36) ltac:(rewrite Q20; exact X37)
ltac:(rewrite Q21; exact X38) ltac:(rewrite Q22; exact X39) ltac:(rewrite Q23; exact X40)
ltac:(rewrite Q3; apply EEreg; reflexivity) ltac:(rewrite Q4; apply EEreg; reflexivity) F24).
Qed.

End t.
