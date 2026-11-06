(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the code table (87 words from 0x8150c), the block pcs, the strlen and memcpy entries, the two separators and the shadow token's base register (s2, atom 18) are rate's; the image facts come from lib/A/RtPgSteps.v; kept_run of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 25d4b718638e is added as w7_kept_run. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBase.v; 107 of its 150 lines of code are new or changed and 100 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): THE PLUMBING the pieces of
   the checking segment M02's head and scan (lib/A/RtPgScanHead.v, RtPgScanSetup.v, RtPgScanOuter.v,
   RtPgScanInner.v) share. Proves no function (kind: segment lemma): each lemma is a fact of the kit's engine
   (lib/Reusable: st_ok, region_ok, Ereg) or of lib/A/RtPgSeg.v's cut lists, used by more than one piece.
     - the entry state of a run whose registers are atoms and that holds no region (sk_entry), with the runtime's
       shadow offset as the extra atom 32 (sk_extra, SKBx, SKspan) for the token engine's shadow checks;
     - an entry register file with some registers written as other atoms plus a constant (sk_sr, sk_regs_ok);
     - a field of a region of the engine's state as a val_mem (sk_field_of_region);
     - a register or cell fact of a cut list, a sub-list of it, and the list at a register file that agrees on
       the list's registers (sk_at_get, sk_at_cell, sk_at_sub, sk_at_keep);
     - the checks' base rs_chk_base at a state that differs from a cut's only in its registers outside sp / gp / tp
       and in an I/O-equal model (sk_chk_base);
     - a register the engine left as an atom of its entry env (sk_reg_atom, sk_reg_is, sk_getr_z, sk_soff). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* ---- the shadow base of a run with no shadow entry: env slot 32 holds the runtime's shadow offset ---- *)
Definition SKBx : sv := SOff 32 0.
Definition SKspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition sk_extra : list word := [Z_to_bv 64 SHADOW_OFF].

(* ---- an entry register file: the atoms, with the registers of ov written as the given svs ---- *)
Definition sk_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.
Lemma sk_regs_ok : forall regs extra (ov : list (bv 5 * sv)),
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs extra) (snd p) = getr regs (fst p)) ov ->
regs_ok (Ereg regs extra) (sk_sr ov) regs.
Proof.
intros regs extra ov Hov. unfold sk_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply regs_ok_pin; [exact Hsr | exact Hr0 | symmetry; exact Hv]. }
apply G. apply regs_ok_Ereg.
Qed.

(* ---- the value of an atom plus an offset ---- *)
Lemma sk_soff : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. apply bv_eq. rewrite denot_SOff, H, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* ---- a register named by Z_to_bv 5 n (the cut lists' form) is the register named by the numeral n ---- *)
Lemma sk_getr_z : forall (regs : bvmap 5 word) (r : bv 5) n, bv_unsigned r = n -> getr regs (Z_to_bv 5 n) = getr regs r.
Proof.
intros regs r n H. f_equal. apply bv_eq. subst n. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (u5_range r). change (bv_modulus 5) with 32. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- the entry state of a run at pc: the registers as atoms, no region, no fact ---- *)
Definition ss_sk (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma sk_entry : forall pc (W : world rsegs) regs memc, 0 <= pc ->
st_ok rsegs (Ereg regs sk_extra) (ss_sk pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc W regs memc Hpc.
rewrite restrict_mkst_fx.
unfold ss_sk. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.

(* ---- a field of a region of the engine's state, as the val_mem it denotes ---- *)
Lemma sk_field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.

(* ---- a register the run left as its own atom holds its value at the run's start ---- *)
Lemma sk_reg_atom : forall E ss ms (H : word -> bool) regs extra (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms H regs extra r HS [HA _] Hr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r); lia). apply ew_Ereg_reg.
Qed.
(* ---- a register the run left as an atom of the entry env holds that atom's register ---- *)
Lemma sk_reg_is : forall E ss ms (H : word -> bool) regs extra (r r' : bv 5) n,
st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros E ss ms H regs extra r r' n HS [HA _] Hr Hn.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r'); lia). apply ew_Ereg_nat. exact Hn.
Qed.

(* ================================ the cut lists ================================ *)
(* a register fact of a list *)
Lemma sk_at_get : forall H mem regs e L r v, rs_at rsegs H mem regs e L -> In (LReg r, v) L ->
getr regs (Z_to_bv 5 r) = w64 v.
Proof.
intros H mem regs e L r v HL Hin. unfold rs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin).
Qed.
(* a cell fact of a list *)
Lemma sk_at_cell : forall H mem regs e L b o v, rs_at rsegs H mem regs e L -> In (LCell b o, v) L ->
val_mem rsegs (mrestrict H mem) (rt_xv e b + o) 8 (v mod 2 ^ 64).
Proof.
intros H mem regs e L b o v HL Hin. unfold rs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin).
Qed.
(* a sub-list of a list of facts *)
Lemma sk_at_sub : forall H mem regs e L L', rs_at rsegs H mem regs e L -> (forall x, In x L' -> In x L) ->
rs_at rsegs H mem regs e L'.
Proof.
intros H mem regs e L L' HL Hs. unfold rs_at in *. rewrite Forall_forall in *. intros x Hx. exact (HL x (Hs x Hx)).
Qed.
(* a list whose registers all lie in kept holds at a register file that agrees on kept *)
Definition sk_locb (kept : list (bv 5)) (f : rt_loc * Z) : bool :=
match fst f with LReg r => existsb (fun c => bv_eqb c (Z_to_bv 5 r)) kept | LCell _ _ => true end.
Lemma sk_at_keep : forall H mem regs regs' e L (kept : list (bv 5)),
(forall r, In r kept -> getr regs' r = getr regs r) -> forallb (sk_locb kept) L = true ->
rs_at rsegs H mem regs e L -> rs_at rsegs H mem regs' e L.
Proof.
intros H mem regs regs' e L kept Hk Hb HL. unfold rs_at in *. rewrite Forall_forall in *.
intros [[r|b o] v] Hx. 2:{ exact (HL _ Hx). }
pose proof (HL _ Hx) as Hv. cbn [rt_at fst snd] in Hv |- *.
pose proof (proj1 (forallb_forall _ _) Hb _ Hx) as Hl. unfold sk_locb in Hl. cbn [fst] in Hl.
apply existsb_exists in Hl as (c & Hc & Hcb). apply bv_eqb_eq in Hcb. subst c.
rewrite (Hk _ Hc). exact Hv.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the checks' base at a state that differs from a cut's only in registers other than sp, gp, tp, and in its
   I/O-equal model *)
Lemma sk_chk_base : forall (cx : rs_scx rsegs) (fx2 : YK11.FPState) rec pat ly2 S2 W2 regs2 mem2 md2 regs3 md3,
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec pat ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem2 md3 (x_k cx) ->
same_io md2 md3 ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec pat ly2 S2 W2 regs3 mem2 md3.
Proof.
intros cx fx2 rec pat ly2 S2 W2 regs2 mem2 md2 regs3 md3 (Hcore & Hrest) HJ3 Hio3 Hk.
split; [|exact Hrest].
unfold rs_core, rs_mid in Hcore |- *.
destruct Hcore as (_ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
split; [exact HJ3|].
split; [intros r Hr; rewrite <- (H234 r Hr); apply Hk; exact Hr|].
split; [exact Hfr|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|].
split; [exact Hmo | exact Hkeep].
Qed.
End e.
End b.

Print Assumptions sk_entry.
Print Assumptions sk_regs_ok.
Print Assumptions sk_field_of_region.
Print Assumptions sk_at_keep.
Print Assumptions sk_chk_base.
