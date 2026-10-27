(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0k.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis Htbl : table_ok segs tbl.
Section g.
Variable P1 : env -> list sv -> bvmap 5 word -> Prop.
Variable P5 : list sv -> bv 32 -> Prop.
Definition st_okP (E : env) (ss : sstate) (ms : machine_state) : Prop :=
P1 E (ss_fregs ss) (ms_fregs ms)
/\ ms_pc_val ms = Z_to_bv 64 (ss_pc ss)
/\ ms_svc_pending ms = None
/\ ms_resv ms = resv_denot E (ss_resv ss)
/\ P5 (ss_fregs ss) (ms_fcsr ms)
/\ ms_rom ms = seg_rom segs
/\ regs_ok E (ss_regs ss) (ms_regs ms)
/\ mem_ok segs E (ms_mem ms) (ss_mem ss)
/\ facts_ok E (ss_facts ss).
Definition st_okP_ecall (E : env) (ss : sstate) (ms : machine_state) : Prop :=
P1 E (ss_fregs ss) (ms_fregs ms)
/\ ms_pc_val ms = Z_to_bv 64 (ss_pc ss)
/\ ms_svc_pending ms = Some (sv_denot E (sr_get (ss_regs ss) 17))
/\ ms_resv ms = resv_denot E (ss_resv ss)
/\ P5 (ss_fregs ss) (ms_fcsr ms)
/\ ms_rom ms = seg_rom segs
/\ regs_ok E (ss_regs ss) (ms_regs ms)
/\ mem_ok segs E (ms_mem ms) (ss_mem ss)
/\ facts_ok E (ss_facts ss).
Lemma lit_add : forall a b, (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma lit_canon : forall a, Z_to_bv 64 (zcanon a) = Z_to_bv 64 a.
Proof. apply Z_to_bv64_canon. Qed.
Lemma pc_plus4 : forall pc, (Z_to_bv 64 pc + Z_to_bv 64 4)%bv = Z_to_bv 64 (pc + 4).
Proof. intros. apply lit_add. Qed.
Lemma sext64_lit : forall {n} (b : bv n), sext 64 b = Z_to_bv 64 (bv_signed b).
Proof. reflexivity. Qed.
Lemma zext64_lit : forall {n} (b : bv n), zext 64 b = Z_to_bv 64 (bv_unsigned b).
Proof. reflexivity. Qed.
Lemma low32_lit : forall z, low32 (Z_to_bv 64 z) = Z_to_bv 32 z.
Proof.
intro z. unfold low32. apply bv_eq.
rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2^64). change (bv_modulus 32) with (2^32).
apply Z.mod_mod_divide. exists (2^32). reflexivity.
Qed.
Lemma sext32_low32 : forall {n} (b : bv n), sext 32 b = low32 (Z_to_bv 64 (bv_signed b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.
Lemma zext32_low32 : forall {n} (b : bv n), zext 32 b = low32 (Z_to_bv 64 (bv_unsigned b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.
Lemma rget_getr : forall c r, rget c r = getr (c_regs c) r.
Proof. intros. reflexivity. Qed.
Lemma addr_of_sound : forall E G a b off,
facts_ok E G -> addr_of a = Some (b, off) ->
sv_denot E a = Z_to_bv 64 (base_val E b + off).
Proof.
intros E G a b off HG H. destruct a; cbn in H; try discriminate; injection H as <- <-; cbn.
- symmetry. apply Z_to_bv64_canon.
- reflexivity.
Qed.
Lemma step_on_fetch : forall ms w,
fetch_word segs (ms_pc_val ms) = Some w ->
RiscvSemantics.step segs ms = decode_exec segs ms w.
Proof. intros ms w H. apply step_on_fetch_compat. exact H. Qed.
Definition mach (fregs : bvmap 5 word) (fcsr : bv 32)
(regs : bvmap 5 word) (pc : word) (resv : option word) (mem : word -> option byte)
: machine_state :=
{| ms_regs := regs; ms_fregs := fregs; ms_pc_val := pc; ms_svc_pending := None;
ms_resv := resv; ms_fcsr := fcsr; ms_mem := mem; ms_rom := seg_rom segs |}.
Lemma st_ok_mach : forall E ss fregs fcsr regs pc resv mem,
P1 E (ss_fregs ss) fregs ->
P5 (ss_fregs ss) fcsr ->
regs_ok E (ss_regs ss) regs ->
pc = Z_to_bv 64 (ss_pc ss) ->
resv = resv_denot E (ss_resv ss) ->
mem_ok segs E mem (ss_mem ss) ->
facts_ok E (ss_facts ss) ->
st_okP E ss (mach fregs fcsr regs pc resv mem).
Proof.
intros E ss fregs fcsr regs pc resv mem HP1 HP5 H1 H2 H3 H4 H5. unfold st_okP, mach; cbn.
split; [exact HP1|]. split; [exact H2|]. split; [reflexivity|]. split; [exact H3|].
split; [exact HP5|]. split; [reflexivity|]. split; [exact H1|]. exact (conj H4 H5).
Qed.
Lemma regs_ok_set' : forall E sr regs rd v e,
regs_ok E sr regs -> sv_denot E e = v ->
regs_ok E (sr_set sr rd e) (if is_x0 rd then regs else bvmap_set rd v regs).
Proof. intros. rewrite <- bv_eqb0_is_x0. apply (regs_ok_set E sr regs rd v e); assumption. Qed.
Lemma rset_core : forall rd v regs fr pc fcsr rv,
rset rd v (Core regs fr pc fcsr rv) = Core (if is_x0 rd then regs else bvmap_set rd v regs) fr pc fcsr rv.
Proof. intros. unfold rset, with_regs. destruct (is_x0 rd); reflexivity. Qed.
Lemma rget_regs : forall regs fr pc fcsr rv r,
rget (Core regs fr pc fcsr rv) r = getr regs r.
Proof. intros. unfold rget, getr. cbn. rewrite bv_eqb0_is_x0. reflexivity. Qed.
Lemma bv_not_w1 : bv_not w1 = Z_to_bv 64 (-2).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma extract_unsigned_mod : forall (k : N) (w : word),
bv_unsigned (bv_extract 0 k w) = bv_unsigned w mod 2 ^ Z.of_N k.
Proof. intros. rewrite bv_extract_unsigned, Z.shiftr_0_r. reflexivity. Qed.
Lemma st_bytes_8 : forall w : word, Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 w)) = st_bytes 1 w.
Proof.
intros w. rewrite extract_unsigned_mod. unfold st_bytes.
rewrite <- (zbytes_mod 1 (bv_unsigned w) 0 (Z.of_N 8)) by (cbn; lia).
rewrite <- Z_to_le_bytes_zbytes. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
Qed.
Lemma st_bytes_16 : forall w : word, Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 w)) = st_bytes 2 w.
Proof.
intros w. rewrite extract_unsigned_mod. unfold st_bytes.
rewrite <- (zbytes_mod 2 (bv_unsigned w) 0 (Z.of_N 16)) by (cbn; lia).
rewrite <- Z_to_le_bytes_zbytes. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
Qed.
Lemma st_bytes_32 : forall w : word, Z_to_le_bytes 4 (bv_unsigned (low32 w)) = st_bytes 4 w.
Proof.
intros w. unfold low32. rewrite extract_unsigned_mod. unfold st_bytes.
rewrite <- (zbytes_mod 4 (bv_unsigned w) 0 (Z.of_N 32)) by (cbn; lia).
rewrite <- Z_to_le_bytes_zbytes. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
Qed.
Lemma st_bytes_64 : forall w : word, Z_to_le_bytes 8 (bv_unsigned w) = st_bytes 8 w.
Proof. intros w. apply Z_to_le_bytes_st. Qed.
Lemma bv_extract_0_64 : forall w : word, bv_extract 0 64 w = w.
Proof.
intros w. apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small.
apply bv_unsigned_in_range.
Qed.
Lemma aligned_dec_sound : forall E G a al,
facts_ok E G -> 0 < al -> aligned_dec G a al = true ->
bv_unsigned (sv_denot E a) mod al = 0.
Proof.
intros E G a al HG Hal H. destruct a; cbn in H; try discriminate.
- apply Z.eqb_eq in H. cbn. rewrite unsigned_lit. exact H.
- destruct (atom_lookup (f_atoms G) n) as [f|] eqn:Hl; [|discriminate].
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hl) as (Hb & Hm & Hk).
rewrite denot_SOff. unfold zcanon, M64.
apply Z.mod_divide in H2; [|lia]. apply Z.mod_divide in H3; [|lia]. apply Z.mod_divide in Hm; [|apply Z.pow_nonzero; lia].
apply Z.mod_divide; [lia|].
assert (Hal64 : (al | 2^64)).
{ destruct H2 as [q Hq]. exists (q * 2^(64 - af_al2 f)).
replace (2^64) with (2^af_al2 f * 2^(64 - af_al2 f)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Hq. lia. }
replace ((bv_unsigned (ew E n) + z) mod 2^64)
with ((bv_unsigned (ew E n) + z) - 2^64 * ((bv_unsigned (ew E n) + z) / 2^64))
by (pose proof (Z.div_mod (bv_unsigned (ew E n) + z) (2^64) ltac:(lia)); lia).
apply Z.divide_sub_r.
+ apply Z.divide_add_r; [|exact H3]. destruct Hm as [q Hq]. destruct H2 as [q' Hq']. exists (q * q'). lia.
+ apply Z.divide_mul_l. exact Hal64.
Qed.
Theorem sym_step_soundP : forall E ss ss' ms,
st_okP E ss ms -> sym_step segs tbl ss = SRun ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_okP E ss' ms'
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros E ss ss' ms HS H.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG); cbn in *.
subst pcv pend rom.
unfold sym_step in H.
destruct (clookup tbl (ss_pc ss)) as [wz|] eqn:Hlk; [|discriminate].
pose proof (Htbl (ss_pc ss) wz Hlk) as Hf. cbv zeta in H.
rewrite (step_on_fetch _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (decode_exec_compat segs). destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec; [discriminate|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hd; [|discriminate].
destruct (isz =? 4) eqn:Hsz; cbn [negb] in H; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz.
assert (HR : forall r, rget (Core regs fregs (Z_to_bv 64 (ss_pc ss)) fcsr resv) r
= sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. rewrite rget_regs. apply Hregs. }
destruct i; try discriminate;
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.with_regs Sem.with_pc Sem.with_resv
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr];
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?HR.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4].
reflexivity.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4].
cbn [sv_denot]. rewrite lit_canon, sext64_lit, lit_add. reflexivity.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] |].
+ cbn [sv_denot]. rewrite lit_canon. symmetry. apply pc_plus4.
+ rewrite lit_canon, sext64_lit, lit_add. reflexivity.
-   destruct (sr_get (ss_regs ss) rs1) as [t| | | | | | | | | |] eqn:Hrs1; try discriminate.
injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] |].
+ cbn [sv_denot]. rewrite lit_canon. symmetry. apply pc_plus4.
+ cbn [sv_denot]. rewrite sext64_lit, lit_add, bv_not_w1.
match goal with |- context [bv_and ?x ?y] => change (bv_and x y) with (alu64 ALU_AND x y) end.
apply zalu64_sound.
-
destruct (decide_cond2 (ss_facts ss) c (sr_get (ss_regs ss) rs1) (sr_get (ss_regs ss) rs2)) as [[|]|] eqn:Hdc;
try discriminate; injection H as <-;
rewrite (decide_cond2_sound E _ _ _ _ _ HG Hdc);
eexists; (split; [reflexivity|]); (split; [|cbn [ms_mem]; apply frame_of_refl]); apply st_ok_mach; cbn; auto.
+ rewrite lit_canon, sext64_lit, lit_add. reflexivity.
+ apply pc_plus4.
-
remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
destruct (addr_of a) as [[b off]|] eqn:Hao; [|discriminate].
destruct (sload segs (ss_facts ss) (ss_mem ss) b off sz signed) as [v|] eqn:Hsl; [|discriminate].
injection H as <-.
pose proof (sload_sound segs E _ mem _ _ _ _ _ v HG Hmem Hsl) as (bs & Hrd & Hv).
assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
{ rewrite <- (addr_of_sound E (ss_facts ss) a b off HG Hao). subst a.
rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
rewrite Haddr.
destruct sz; cbn [nbytes nbits] in Hrd, Hv;
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite ov_rdn, Hrd; rewrite ?rset_core;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
eexists; (split; [reflexivity|]); (split; [|cbn [ms_mem]; apply frame_of_refl]);
(apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4]);
rewrite Hv, ?bv_extract_0_64; cbn [load_result nbits]; destruct signed; reflexivity.
-
destruct (ss_resv ss) as [rv0|] eqn:Hrv; [discriminate|]. cbn in Hresv. subst resv.
remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
destruct (addr_of a) as [[b off]|] eqn:Hao; [|discriminate].
destruct (sstore (ss_mem ss) b off sz (sr_get (ss_regs ss) rs2)) as [m'|] eqn:Hst; [|discriminate].
injection H as <-.
pose proof (sstore_sound segs E mem _ _ _ _ _ m' Hmem Hst) as [Hok Hmem'].
assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
{ rewrite <- (addr_of_sound E (ss_facts ss) a b off HG Hao). subst a.
rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
rewrite Haddr.
destruct sz; cbn [nbytes nbits] in Hok, Hmem';
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite Hok; unfold inval_resv;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?st_bytes_8, ?st_bytes_16, ?st_bytes_32, ?st_bytes_64, write_to_mem_wbytes;
eexists; (split; [reflexivity|]);
(split; [apply st_ok_mach; cbn; auto; apply pc_plus4
| cbn [ms_mem]; eapply store_region_frame; [exact Hmem| | cbn; lia] ]).
all: unfold sstore in Hst; unfold st_bytes; rewrite length_zbytes; exact Hst.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4].
rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4].
rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite zext64_lit. reflexivity.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4].
rewrite s_alu2_sound by exact HG. reflexivity.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4].
rewrite s_aluw3_sound by exact HG. cbn [sv_denot]. rewrite sext32_low32. reflexivity.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4].
rewrite s_aluw3_sound by exact HG. cbn [sv_denot]. rewrite zext32_low32. reflexivity.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4].
rewrite s_aluw3_sound by exact HG. reflexivity.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl]. apply st_ok_mach; cbn; auto. apply pc_plus4.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl]. apply st_ok_mach; cbn; auto. apply pc_plus4.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4].
rewrite s_md_sound. reflexivity.
-   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4].
rewrite s_mdw_sound. reflexivity.
-
destruct (aligned_dec (ss_facts ss) (sr_get (ss_regs ss) rs1) (amo_bytes_of w)) eqn:Hal;
cbn [negb] in H; [|discriminate].
destruct (addr_of (sr_get (ss_regs ss) rs1)) as [[b off]|] eqn:Hao; [|discriminate].
destruct (sload segs (ss_facts ss) (ss_mem ss) b off (amo_sz w) true) as [v|] eqn:Hsl; [|discriminate].
injection H as <-.
pose proof (sload_sound segs E _ mem _ _ _ _ _ v HG Hmem Hsl) as (bs & Hrd & Hv).
pose proof (addr_of_sound E (ss_facts ss) _ b off HG Hao) as Haddr.
assert (Hamo : amo_aligned w (sv_denot E (sr_get (ss_regs ss) rs1)) = true).
{ unfold amo_aligned. apply Z.eqb_eq.
apply (aligned_dec_sound E (ss_facts ss)); [exact HG| destruct w; cbn; lia |].
destruct w; exact Hal. }
rewrite Hamo. cbn [negb]. rewrite Haddr in *.
destruct w; cbn [amo_sz nbytes nbits] in Hrd, Hv;
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite ov_rdn, Hrd; rewrite ?rset_core;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
eexists; (split; [reflexivity|]); (split; [|cbn [ms_mem]; apply frame_of_refl]);
(apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4 | rewrite Haddr; reflexivity]);
rewrite Hv, ?bv_extract_0_64; cbn [load_result nbits]; reflexivity.
-
destruct (aligned_dec (ss_facts ss) (sr_get (ss_regs ss) rs1) (amo_bytes_of w)) eqn:Hal;
cbn [negb] in H; [|discriminate].
assert (Hamo : amo_aligned w (sv_denot E (sr_get (ss_regs ss) rs1)) = true).
{ unfold amo_aligned. apply Z.eqb_eq.
apply (aligned_dec_sound E (ss_facts ss)); [exact HG| destruct w; cbn; lia |].
destruct w; exact Hal. }
rewrite Hamo. cbn [negb].
destruct (ss_resv ss) as [a'|] eqn:Hrv; cbn in Hresv; subst resv.
+ destruct (sv_eqb a' (sr_get (ss_regs ss) rs1)) eqn:Heq; cbn [negb] in H; [|discriminate].
apply sv_eqb_eq in Heq. subst a'.
destruct (addr_of (sr_get (ss_regs ss) rs1)) as [[b off]|] eqn:Hao; [|discriminate].
destruct (sstore (ss_mem ss) b off (amo_sz w) (sr_get (ss_regs ss) rs2)) as [m'|] eqn:Hst; [|discriminate].
injection H as <-.
pose proof (sstore_sound segs E mem _ _ _ _ _ m' Hmem Hst) as [Hok Hmem'].
pose proof (addr_of_sound E (ss_facts ss) _ b off HG Hao) as Haddr.
rewrite Z.eqb_refl. rewrite Haddr in *.
destruct w; cbn [amo_sz nbytes nbits] in Hok, Hmem';
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite Hok; rewrite ?rset_core;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?st_bytes_32, ?st_bytes_64, write_to_mem_wbytes;
eexists; (split; [reflexivity|]);
(split; [apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs| reflexivity] | apply pc_plus4]
| cbn [ms_mem]; eapply store_region_frame; [exact Hmem| | cbn; lia] ]).
all: unfold sstore in Hst; unfold st_bytes; rewrite length_zbytes; exact Hst.
+ injection H as <-. rewrite ?rset_core.
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
eexists; (split; [reflexivity|]); (split; [|cbn [ms_mem]; apply frame_of_refl]).
apply st_ok_mach; cbn; auto; [apply regs_ok_set'; [exact Hregs| reflexivity] | apply pc_plus4].
Qed.
Theorem sym_step_ecallP : forall E ss ss' ms,
st_okP E ss ms -> sym_step segs tbl ss = SEcall ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_okP_ecall E ss' ms'
/\ ms_mem ms' = ms_mem ms /\ ss' = ss.
Proof.
intros E ss ss' ms HS H.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG); cbn in *.
subst pcv pend rom.
unfold sym_step in H.
destruct (clookup tbl (ss_pc ss)) as [wz|] eqn:Hlk; [|discriminate].
pose proof (Htbl (ss_pc ss) wz Hlk) as Hf. cbv zeta in H.
rewrite (step_on_fetch _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (decode_exec_compat segs). destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec.
2:{ destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|]; [|discriminate].
destruct (isz =? 4); cbn [negb] in H; [|discriminate]. destruct i; try discriminate.
all: repeat match type of H with
| context [match ?x with _ => _ end] => destruct x; try discriminate
end. }
injection H as <-. eexists. split; [reflexivity|]. split; [|split; reflexivity].
unfold st_okP_ecall; cbn.
split; [exact Hfr|]. split; [reflexivity|]. split.
{ unfold ms_reg. cbn. rewrite <- (Hregs 17%bv). unfold getr. reflexivity. }
split; [exact Hresv|]. split; [exact Hfcsr|]. split; [reflexivity|]. split; [exact Hregs|].
exact (conj Hmem HG).
Qed.
Lemma sym_step_skeleton : forall ss ss',
sym_step segs tbl ss = SRun ss' -> skeleton (ss_mem ss') = skeleton (ss_mem ss).
Proof.
intros ss ss' H. unfold sym_step in H.
destruct (clookup tbl (ss_pc ss)) as [wz|]; [|discriminate]. cbv zeta in H.
destruct (is_ecall (Z_to_bv 32 wz)); [discriminate|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|]; [|discriminate].
destruct (isz =? 4); cbn [negb] in H; [|discriminate].
destruct i; try discriminate;
repeat match type of H with
| context [sstore ?rs ?b ?off ?sz ?v] =>
destruct (sstore rs b off sz v) eqn:?Hst; [|try discriminate]
| context [match ?x with _ => _ end] => destruct x; try discriminate
end;
try (injection H as <-; cbn; try reflexivity).
all: try (injection H as <-; cbn; eapply store_region_skeleton; eassumption).
all: try (eapply store_region_skeleton; eassumption).
Qed.
Theorem sym_run_soundP : forall fuel E ss ss' st ms,
st_okP E ss ms -> sym_run segs tbl fuel ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with
| RS_ecall => st_okP_ecall E ss' ms'
| _ => st_okP E ss' ms'
end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros E ss ss' st ms HS H; cbn [sym_run] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
- destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hs.
+ destruct (sym_step_soundP E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hfr1).
pose proof (sym_step_skeleton ss ss1 Hs) as Hsk1.
destruct (IH E ss1 ss' st ms1 HS1 H) as (ms' & Hms & HS' & Hsk & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS'|]. split; [congruence|].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr].
+ injection H as <- <-.
destruct (sym_step_ecallP E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hm & Hss). subst ss1.
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS1|]. split; [reflexivity|]. rewrite Hm. apply frame_of_refl.
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
Qed.
Theorem sym_run_to_soundP : forall fuel stop E ss ss' st ms,
st_okP E ss ms -> sym_run_to segs tbl fuel stop ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with
| RS_ecall => st_okP_ecall E ss' ms'
| _ => st_okP E ss' ms'
end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros stop E ss ss' st ms HS H; cbn [sym_run_to] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
- destruct (ss_pc ss =? stop).
{ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl]. }
destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hs.
+ destruct (sym_step_soundP E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hfr1).
pose proof (sym_step_skeleton ss ss1 Hs) as Hsk1.
destruct (IH stop E ss1 ss' st ms1 HS1 H) as (ms' & Hms & HS' & Hsk & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS'|]. split; [congruence|].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr].
+ injection H as <- <-.
destruct (sym_step_ecallP E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hm & Hss). subst ss1.
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS1|]. split; [reflexivity|]. rewrite Hm. apply frame_of_refl.
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
Qed.
End g.
Section h.
Context {fx : FPState}.
Definition P1_pin : env -> list sv -> bvmap 5 word -> Prop := fun _ _ f => f = fp_regs.
Definition P5_pin : list sv -> bv 32 -> Prop := fun _ c => c = fp_csr.
Lemma st_ok_P : forall E ss ms, st_ok segs E ss ms <-> st_okP P1_pin P5_pin E ss ms.
Proof. intros. split; exact (fun H => H). Qed.
Lemma st_ok_machL : forall E ss regs pc resv mem,
regs_ok E (ss_regs ss) regs ->
pc = Z_to_bv 64 (ss_pc ss) ->
resv = resv_denot E (ss_resv ss) ->
mem_ok segs E mem (ss_mem ss) ->
facts_ok E (ss_facts ss) ->
st_ok segs E ss (mach fp_regs fp_csr regs pc resv mem).
Proof. intros. apply (st_ok_mach P1_pin P5_pin); first [assumption | reflexivity]. Qed.
Theorem sym_step_sound : forall E ss ss' ms,
st_ok segs E ss ms -> sym_step segs tbl ss = SRun ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok segs E ss' ms'
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof. exact (sym_step_soundP P1_pin P5_pin). Qed.
Theorem sym_step_ecall : forall E ss ss' ms,
st_ok segs E ss ms -> sym_step segs tbl ss = SEcall ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok_ecall segs E ss' ms'
/\ ms_mem ms' = ms_mem ms /\ ss' = ss.
Proof. exact (sym_step_ecallP P1_pin P5_pin). Qed.
Theorem sym_run_sound : forall fuel E ss ss' st ms,
st_ok segs E ss ms -> sym_run segs tbl fuel ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with
| RS_ecall => st_ok_ecall segs E ss' ms'
| _ => st_ok segs E ss' ms'
end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof. exact (sym_run_soundP P1_pin P5_pin). Qed.
Theorem sym_run_to_sound : forall fuel stop E ss ss' st ms,
st_ok segs E ss ms -> sym_run_to segs tbl fuel stop ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with
| RS_ecall => st_ok_ecall segs E ss' ms'
| _ => st_ok segs E ss' ms'
end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof. exact (sym_run_to_soundP P1_pin P5_pin). Qed.
End h.
Definition P1_trk : env -> list sv -> bvmap 5 word -> Prop := fregs_ok.
Definition P5_trk : list sv -> bv 32 -> Prop := fun _ c => frm_zero c.
Lemma st_okF_P : forall E ss ms, st_okF segs E ss ms <-> st_okP P1_trk P5_trk E ss ms.
Proof. intros. split; exact (fun H => H). Qed.
Theorem sym_step_soundF : forall E ss ss' ms,
st_okF segs E ss ms -> sym_step segs tbl ss = SRun ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_okF segs E ss' ms'
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof. exact (sym_step_soundP P1_trk P5_trk). Qed.
Theorem sym_step_ecallF : forall E ss ss' ms,
st_okF segs E ss ms -> sym_step segs tbl ss = SEcall ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_okF_ecall segs E ss' ms'
/\ ms_mem ms' = ms_mem ms /\ ss' = ss.
Proof. exact (sym_step_ecallP P1_trk P5_trk). Qed.
Theorem sym_run_soundF : forall fuel E ss ss' st ms,
st_okF segs E ss ms -> sym_run segs tbl fuel ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with
| RS_ecall => st_okF_ecall segs E ss' ms'
| _ => st_okF segs E ss' ms'
end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof. exact (sym_run_soundP P1_trk P5_trk). Qed.
Theorem sym_run_to_soundF : forall fuel stop E ss ss' st ms,
st_okF segs E ss ms -> sym_run_to segs tbl fuel stop ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with
| RS_ecall => st_okF_ecall segs E ss' ms'
| _ => st_okF segs E ss' ms'
end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof. exact (sym_run_to_soundP P1_trk P5_trk). Qed.
End d.
