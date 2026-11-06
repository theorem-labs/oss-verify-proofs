(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b01 (its code table, wx / segs_low lemmas, save-slot region, ck_sr / ck_facts / regs_ok_override / ck_regs_ok / ck_lit / ck_atom, the entry-state lemma, same_io_wvb_ck, ck_kept_run and the run / keep / leaf tactics) and proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at 5afd8b87436 (pa_i_memset_at, pa_i_regs_kept, pa_i_region_nth, pa_i_field, pa_i_soff, pa_i_cs / pa_i_notin / pa_i_pres and the reg / region tactics) for reac-pw/fuzz_rate's image B (fuzz_rate.asan-ubsan): the image is AsanUbsan, the table is pod_write_ent's 194 words, the frame is 48 bytes, the intrinsic lemma is stated for both memory operations, and the read-only extents are image B's GOT slot and shadow-offset cell. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/PweKit.v at d75b4b9c245; module paths fuzz_rate -> fuzz_role, the image module fuzz_role's AsanUbsan, every address and .got cell moved from fuzz_rate.asan-ubsan to fuzz_role.asan-ubsan by symbol + offset and checked on fuzz_role.asan-ubsan's .symtab and words; ledger provenance/evidence/reloc/AU-Pwe.tsv. *)
(* The walk kit of pod_write_ent on reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address is measured on its unstripped
   twin sha256 dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a). Proves no function (kind: walk
   kit): the code table the engine reads pod_write_ent from, the entry states of its four runs, the law of the two
   runtime calls it makes, and the tactics the walk uses.

   THE FUNCTION, 0x82bac, 776 bytes, 194 words; the four runs the walk makes are cut at its two calls and at the
   pad (whose value needs a register pinned to the pad it has just computed):
     R1 0x82bac .. 0x82d78  prologue; the alignment tests of e and pp; the shadow-offset cell through the GOT;
                            put32 e->size and put32 e->type at pp + len and pp + len + 4, each under its capacity
                            guard, its two UBSan tests and its two instrumented checks; the len cell's check and
                            its two updates; then `jal` __asan_memcpy(pp + len + 8, e + 8, size).
     R2 0x82d7c .. 0x82d98  the len cell's check and its update to len + 8 + size; `negw` and `andi 7`, the pad.
     R3 0x82d98 .. 0x82dc0  the pad's capacity guard and its two UBSan tests; `jal` __asan_memset(pp + len + 8 +
                            size, 0, pad).
     R4 0x82dc4 .. 0x82df0  the len cell's check, its update to len + n, the epilogue and `ret`.
   The error path (the calls of an __asan_report_ entry at 0x82df8 .. 0x82eb0) and the trap `unimp` 0x82df4 are
   never stepped: every instrumented check reads a shadow byte the shadow entries of pp's block and of e's object
   make addressable, and every UBSan test is refuted by the contract's arithmetic premises.

   THE ENGINE'S ENVIRONMENT. Registers are atoms 0 .. 31 (atom 10 = pp, atom 11 = e at entry); the extra atoms are
     32 the runtime's shadow offset K, 33 len, 34 e_size, 35 e_type, 36 pp + len.
   The read-only extents are image B's: the GOT slot [0x9aad0, 0x9aad8), whose 8 bytes are the address of the
   shadow-offset cell 0xa3678, and that cell, whose 8 bytes are K. Both are given by the runtime invariant's
   constant law (YG0d.v AR_const_law) and the symbol record's as_got_shadow / as_shadow_cell. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import PweSpec.
From OSSVerify.reac_pw.fuzz_role.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image and the code table ---- *)
Definition rsegs := AsanUbsan.M.loaded_segments.
Definition PWE_A : Z := 0x82bac.
Definition PWE_MEMCPY : Z := 0x5116c.
Definition PWE_MEMSET : Z := 0x51608.
(* the 194 instruction words 0x82bac .. 0x82eb0: the whole function, its traps and its error path *)
Definition pwe_tbl : ctable := build_table rsegs PWE_A 194 TEmpty.
Lemma pwe_tbl_ok : table_ok rsegs pwe_tbl.
Proof. apply build_table_ok0. unfold PWE_A. lia. Qed.
Lemma pwe_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma pwe_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

(* ---- the shadow base: env slot 32 ---- *)
Definition PWE_Bx : sv := SOff 32 0.
Definition PWE_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pwe_extra (l : list Z) : list word := Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) l.
(* image B's GOT slot and the runtime's shadow-offset cell *)
Definition PWE_GOT : Z := 0x9aad0.
Definition PWE_CELL : Z := 0xa3678.
Definition pwe_got_region : YP09.region :=
YP09.mkRegion None PWE_GOT (PWE_GOT + 8) 0 0 [YP09.mkChunk PWE_GOT (CVal 8 (SLit PWE_CELL))].
Definition pwe_cell_region : YP09.region :=
YP09.mkRegion None PWE_CELL (PWE_CELL + 8) 0 0 [YP09.mkChunk PWE_CELL (CVal 8 (SOff 32 0))].
(* the 48-byte save slot [sp - 48, sp) *)
Definition pwe_stack_region : YP09.region := YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [].

(* ---- registers: sr_atoms with the overrides a register already has ---- *)
Definition pwe_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.
Lemma regs_ok_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
Lemma pwe_regs_ok : forall regs extra (ov : list (bv 5 * sv)),
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs extra) (snd p) = getr regs (fst p)) ov ->
regs_ok (Ereg regs extra) (pwe_sr ov) regs.
Proof.
intros regs extra ov Hov. unfold pwe_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.
Lemma pwe_lit : forall E v, sv_denot E (SLit v) = w64 v.
Proof. intros E v. reflexivity. Qed.
Lemma pwe_soff : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. apply bv_eq. rewrite denot_SOff, H, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
Lemma pwe_zneg : forall z, - M64 <= z < 0 -> zcanon z = z + M64.
Proof.
intros z Hz. unfold zcanon. rewrite <- (Z_mod_plus_full z 1 M64). rewrite Z.mul_1_l. apply Z.mod_small. lia.
Qed.

(* ---- registers kept across a run and across a call ---- *)
Definition pwe_nz : list (bv 5) :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma pwe_bv5_cases : forall r : bv 5, bv_unsigned r <> 0 ->
bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 5 \/
bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/ bv_unsigned r = 10 \/
bv_unsigned r = 11 \/ bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/
bv_unsigned r = 16 \/ bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/
bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/
bv_unsigned r = 26 \/ bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30 \/
bv_unsigned r = 31.
Proof. intros r Hr. pose proof (u5_range r) as Hb. lia. Qed.
Lemma pwe_in_nz : forall r : bv 5, bv_unsigned r <> 0 -> In r pwe_nz.
Proof.
intros r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r).
pose proof (pwe_bv5_cases r Hr) as H.
repeat (destruct H as [H|H]; [rewrite H; cbv [pwe_nz In]; repeat (first [left; apply bv_eq; reflexivity | right]) |]).
rewrite H. cbv [pwe_nz In]. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
(* the registers the two calls may change: ra, t0-t2, a0-a7, t3-t6 (the caller-saved set) *)
Definition pwe_clob : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Lemma pwe_cs : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pwe_clob -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr Hn. unfold acallee_saved.
pose proof (pwe_bv5_cases r Hr) as H.
repeat (destruct H as [H|H];
  [ first [ lia
          | exfalso; apply Hn; rewrite <- (Z_to_bv_bv_unsigned 5 r), H; cbv [pwe_clob In];
            repeat (first [left; apply bv_eq; reflexivity | right]) ] |]).
first [ lia
      | exfalso; apply Hn; rewrite <- (Z_to_bv_bv_unsigned 5 r), H; cbv [pwe_clob In];
        repeat (first [left; apply bv_eq; reflexivity | right]) ].
Qed.
Lemma pwe_notin : forall r : bv 5, existsb (fun c => bv_eqb c r) pwe_clob = false -> ~ In r pwe_clob.
Proof.
intros r H Hin. assert (Ht : existsb (fun c => bv_eqb c r) pwe_clob = true).
{ apply existsb_exists. exists r. split; [exact Hin | unfold bv_eqb; apply Z.eqb_refl]. }
rewrite H in Ht. discriminate Ht.
Qed.
Lemma pwe_pres : forall (r0 r1 : bvmap 5 word) (r : bv 5), aregs_preserved r0 r1 ->
bv_unsigned r <> 0 -> ~ In r pwe_clob -> getr r1 r = getr r0 r.
Proof.
intros r0 r1 r HP Hr Hn. pose proof (HP (bv_unsigned r) (pwe_cs r Hr Hn)) as H.
rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
Ltac pwe_keep_reg KR :=
apply KR; [let Hz := fresh "Hz" in intro Hz; vm_compute in Hz; discriminate Hz | apply pwe_notin; vm_compute; reflexivity].

Section k. Context {fx : YK11.FPState}.
Lemma pwe_regs_kept : forall E ss ms regs0 sr0 (H : word -> bool) (clob : list (bv 5)),
st_ok rsegs E ss (restrict H ms) -> regs_ok E sr0 regs0 ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || sv_eqb (sr_get (ss_regs ss) r) (sr_get sr0 r)) pwe_nz = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 sr0 H clob HS HR Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (pwe_in_nz r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. symmetry. apply HR.
Qed.
Lemma pwe_region_nth : forall H E ss ms i r,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros H E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma pwe_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
End k.

(* the symbolic value of register r at the end of a run *)
Ltac pwe_reg HS r Hn :=
lazymatch type of HS with st_ok ?sg ?E ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Hn : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg sg Hh E ss ms r HS)
end.
(* region i of the state at the end of a run *)
Ltac pwe_regn HS i Hn :=
lazymatch type of HS with st_ok ?sg ?E ?ss (restrict ?Hh ?ms) =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
assert (Hn : region_ok sg E (mrestrict Hh (ms_mem ms)) rg) by (apply (pwe_region_nth Hh E ss ms i rg HS); vm_compute; reflexivity)
end end.
(* the write windows of a run's entry state lie in the zone the goal names *)
Ltac pwe_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => rewrite Hu in Hb end; lia | ]); destruct Hr.
Lemma same_io_wvb_pwe : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a run keeps every byte outside the zone its write windows lie in *)
Lemma pwe_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Ltac pwe_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (pwe_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* The write-range obligation of a run whose only writable window is the 48-byte save slot [sp - 48, sp): it lies
   in the caller's stack allowance (the contract's two window premises) [RPgCheck.v awr_stk]. *)
Ltac pwe_awr_stk :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew E 2) = ?spv |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
  [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ]
end end.
Ltac pwe_run_awr awr stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok pwe_tbl_ok HS HJ SHOK PWE_Bspan stop; [awr | ] end.
Ltac pwe_run stop := pwe_run_awr pwe_awr_stk stop.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws rsegs B.

(* __asan_memcpy's and __asan_memset's contract as a block [YCbq.v aj_intrin_at], with the I/O state kept
   (same_io from the contract's same_but_materialized). *)
Lemma pwe_intrin_at : forall op pc, aintrin_realizes rsegs B op pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
(match op with
 | OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok rsegs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
   range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) x n)
 | OSet => True end) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) =
 match op with OCpy => aview rsegs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof using LAWS.
intros op pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hop.
pose proof pwe_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok rsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  destruct (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
  split; [apply (apresent_writable rsegs); exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hop). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS Hsegs STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; zlia].
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [apply same_io_materialized; exact Hsame|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr | exact Hpres2].
Qed.
End d.
End b.
