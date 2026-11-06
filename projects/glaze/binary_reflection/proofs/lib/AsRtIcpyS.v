(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpy. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpy.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
(* [comment removed for export] *)
Local Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.

Open Scope bv_scope.


(* [comment removed for export] *)
Ltac gresr := repeat (first [ rewrite getr_same by (apply reg_neq_of_eqb; reflexivity)
                            | rewrite getr_other by (apply reg_neq_of_eqb; reflexivity) ]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_andi_m8 : forall x : word, v_andi x (-8) = Z_to_bv 64 (down8 (bv_unsigned x)).
Proof using.
  intros x. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite land_m8 by lia. (lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end). f_equal. pose proof (Z.div_mod (bv_unsigned x) 8 ltac:(lia)). lia.
Qed.

Lemma v_andi_7 : forall x : word, v_andi x 7 = Z_to_bv 64 (bv_unsigned x mod 8).
Proof using. intros x. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). change (bv_wrap 64 7) with 7%Z. rewrite land_7 by lia. reflexivity. Qed.


Lemma Z_to_bv64_addm : forall z m, Z_to_bv 64 (z + 2 ^ 64 * m)%Z = Z_to_bv 64 z.
Proof using.
  intros z m. apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Z.mul_comm, Z.mod_add by lia. reflexivity.
Qed.

Lemma Sh_bounds : forall a, (0x10007fff8000 <= a < 0x800000000000)%Z -> (0x27fff7000 <= Sh a < 0x10007fff8000)%Z.
Proof using.
  intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_le_mono 0x10007fff8000 a 8 ltac:(lia) ltac:(lia)) as H1.
  change (0x10007fff8000 / 8)%Z with 2199291686912%Z in H1.
  pose proof (Z.div_lt_upper_bound a 8 0x100000000000 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma down8_le : forall a, (0 <= a)%Z -> (a - 7 <= down8 a <= a)%Z /\ (down8 a mod 8 = 0)%Z.
Proof using.
  intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end). pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  split; [lia|]. apply Z.mod_mul. lia.
Qed.

Lemma Sh_mono : forall a b, (a <= b)%Z -> (Sh a <= Sh b)%Z.
Proof using. intros a b H. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record icps_tab_ok (segs : list Segment) (t : icpy_tab) : Prop := ICPSOK {
  iso_icpy : icpy_tab_ok segs t;
  iso_g116 : gload segs (it_base t) 116 13 (mt_g_shoff (rt_m2s (it_rip t)));
  iso_g188 : gload segs (it_base t) 188 13 (mt_g_shoff (rt_m2s (it_rip t))) }.

(* [comment removed for export] *)
Record icpsH (segs : list Segment) (t : icpy_tab) (mem : word -> option byte)
       (dst src : word) (n : Z) (bs : list byte) (ra sp : word) (fl : byte)
       (s1s : byte) (w0s w1s : word) (s1d : byte) (w0d w1d : word) : Prop := ICPSH {
  is_mc : mcH segs mem dst src n bs;
  is_n : (1 <= n <= 64)%Z;
  is_g_flag : rdn segs mem (Z_to_bv 64 (it_g_flag t)) 8 = Some (LE8 (Z_to_bv 64 (it_p_flag t)));
  is_flag : rdn segs mem (Z_to_bv 64 (it_p_flag t)) 1 = Some [fl];
  is_fl : bv_unsigned fl <> 0%Z;
  is_rmc : rdn segs mem (Z_to_bv 64 (it_c_rmc t)) 8 = Some (LE8 (it_mcp t));
  is_g_shoff : rdn segs mem (Z_to_bv 64 (mt_g_shoff (rt_m2s (it_rip t)))) 8 = Some (LE8 (Z_to_bv 64 (mt_p_shoff (rt_m2s (it_rip t)))));
  is_shoff : rdn segs mem (Z_to_bv 64 (mt_p_shoff (rt_m2s (it_rip t)))) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000));
  is_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 80)%Z
               [it_g_flag t; it_p_flag t; it_c_rmc t; mt_g_shoff (rt_m2s (it_rip t)); mt_p_shoff (rt_m2s (it_rip t))];
  is_src : (0x10007fff8000 <= bv_unsigned src)%Z /\ (bv_unsigned src + n + 8 <= 0x800000000000)%Z;
  is_dst : (0x10007fff8000 <= bv_unsigned dst)%Z /\ (bv_unsigned dst + n + 8 <= 0x800000000000)%Z;
  (* [comment removed for export] *)
  is_s1s : rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned src + n - 1))) 1 = Some [s1s];
  is_s1sok : (bv_unsigned s1s = 0 \/ (bv_unsigned src + n - 1) mod 8 < bv_unsigned s1s < 128)%Z;
  is_zs : forall a : word, (Sh (bv_unsigned src) <= bv_unsigned a < Sh (bv_unsigned src + n - 1))%Z ->
            rdn segs mem a 1 = Some [Z_to_bv 8 0];
  is_w0s : rdn segs mem (Z_to_bv 64 (down8 (Sh (bv_unsigned src)))) 8 = Some (LE8 w0s);
  is_w1s : rdn segs mem (Z_to_bv 64 (down8 (Sh (bv_unsigned src + n - 1)))) 8 = Some (LE8 w1s);
  (* [comment removed for export] *)
  is_s1d : rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned dst + n - 1))) 1 = Some [s1d];
  is_s1dok : (bv_unsigned s1d = 0 \/ (bv_unsigned dst + n - 1) mod 8 < bv_unsigned s1d < 128)%Z;
  is_zd : forall a : word, (Sh (bv_unsigned dst) <= bv_unsigned a < Sh (bv_unsigned dst + n - 1))%Z ->
            rdn segs mem a 1 = Some [Z_to_bv 8 0];
  is_w0d : rdn segs mem (Z_to_bv 64 (down8 (Sh (bv_unsigned dst)))) 8 = Some (LE8 w0d);
  is_w1d : rdn segs mem (Z_to_bv 64 (down8 (Sh (bv_unsigned dst + n - 1)))) 8 = Some (LE8 w1d);
  (* [comment removed for export] *)
  is_sp : (0x10007fff8000 + 2160 <= bv_unsigned sp)%Z /\ (bv_unsigned sp < 2 ^ 64)%Z;
  is_stk : store_ok segs mem (at_ sp (-80)) 80 = true;
  is_src_stk : (bv_unsigned src + n <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned src)%Z;
  is_dst_stk : (bv_unsigned dst + n <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned dst)%Z;
  is_ret : ret_ok ra }.

Section ICPS.
  Variable segs : list Segment.
  Variable base : word.
  Variable mcp : word.
  Variables g_flag p_flag c_rmc g_shoff p_shoff : Z.
  Hypothesis HCODE : code_ato segs base 0 icpy_words.
  Hypothesis MCP : code_at segs mcp 0 mmemcpy_words.
  Hypothesis G52 : gload segs base 52 13 g_flag.
  Hypothesis G116 : gload segs base 116 13 g_shoff.
  Hypothesis G188 : gload segs base 188 13 g_shoff.
  Hypothesis G244 : gload segs base 244 13 c_rmc.
  Hypothesis Hbase : (bv_unsigned base mod 2 = 0)%Z /\ (bv_unsigned base + 20000 < 2 ^ 64)%Z.
  Hypothesis Hmcp : ret_ok mcp.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_6d960.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_6d964.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_6d968.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_6d96c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_6d970.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_6d974.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_6d978.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_6d97c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_6d980.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_6d984.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_6d988.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_6d98c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 11 _ HCODE eq_refl). Qed.
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_6d990.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_6d99c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_6d9a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_6d9a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_6d9a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_6d9ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_6d9b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_6d9b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_6d9b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo92 : fetch_word segs (at_ base 92) = Some W_6d9bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 23 _ HCODE eq_refl). Qed.
  Lemma Fo96 : fetch_word segs (at_ base 96) = Some W_6d9c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 24 _ HCODE eq_refl). Qed.
  Lemma Fo100 : fetch_word segs (at_ base 100) = Some W_6d9c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 25 _ HCODE eq_refl). Qed.
  Lemma Fo104 : fetch_word segs (at_ base 104) = Some W_6d9c8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 26 _ HCODE eq_refl). Qed.
  Lemma Fo108 : fetch_word segs (at_ base 108) = Some W_6d9cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 27 _ HCODE eq_refl). Qed.
  Lemma Fo112 : fetch_word segs (at_ base 112) = Some W_6d9d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 28 _ HCODE eq_refl). Qed.
  Lemma Fo124 : fetch_word segs (at_ base 124) = Some W_6d9dc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 31 _ HCODE eq_refl). Qed.
  Lemma Fo128 : fetch_word segs (at_ base 128) = Some W_6d9e0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 32 _ HCODE eq_refl). Qed.
  Lemma Fo132 : fetch_word segs (at_ base 132) = Some W_6d9e4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 33 _ HCODE eq_refl). Qed.
  Lemma Fo136 : fetch_word segs (at_ base 136) = Some W_6d9e8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 34 _ HCODE eq_refl). Qed.
  Lemma Fo140 : fetch_word segs (at_ base 140) = Some W_6d9ec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 35 _ HCODE eq_refl). Qed.
  Lemma Fo144 : fetch_word segs (at_ base 144) = Some W_6d9f0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 36 _ HCODE eq_refl). Qed.
  Lemma Fo148 : fetch_word segs (at_ base 148) = Some W_6d9f4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 37 _ HCODE eq_refl). Qed.
  Lemma Fo152 : fetch_word segs (at_ base 152) = Some W_6d9f8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 38 _ HCODE eq_refl). Qed.
  Lemma Fo156 : fetch_word segs (at_ base 156) = Some W_6d9fc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 39 _ HCODE eq_refl). Qed.
  Lemma Fo160 : fetch_word segs (at_ base 160) = Some W_6da00.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 40 _ HCODE eq_refl). Qed.
  Lemma Fo164 : fetch_word segs (at_ base 164) = Some W_6da04.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 41 _ HCODE eq_refl). Qed.
  Lemma Fo168 : fetch_word segs (at_ base 168) = Some W_6da08.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 42 _ HCODE eq_refl). Qed.
  Lemma Fo172 : fetch_word segs (at_ base 172) = Some W_6da0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo176 : fetch_word segs (at_ base 176) = Some W_6da10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo180 : fetch_word segs (at_ base 180) = Some W_6da14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 45 _ HCODE eq_refl). Qed.
  Lemma Fo184 : fetch_word segs (at_ base 184) = Some W_6da18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 46 _ HCODE eq_refl). Qed.
  Lemma Fo196 : fetch_word segs (at_ base 196) = Some W_6da24.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 49 _ HCODE eq_refl). Qed.
  Lemma Fo200 : fetch_word segs (at_ base 200) = Some W_6da28.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 50 _ HCODE eq_refl). Qed.
  Lemma Fo204 : fetch_word segs (at_ base 204) = Some W_6da2c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 51 _ HCODE eq_refl). Qed.
  Lemma Fo208 : fetch_word segs (at_ base 208) = Some W_6da30.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 52 _ HCODE eq_refl). Qed.
  Lemma Fo212 : fetch_word segs (at_ base 212) = Some W_6da34.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 53 _ HCODE eq_refl). Qed.
  Lemma Fo216 : fetch_word segs (at_ base 216) = Some W_6da38.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 54 _ HCODE eq_refl). Qed.
  Lemma Fo220 : fetch_word segs (at_ base 220) = Some W_6da3c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 55 _ HCODE eq_refl). Qed.
  Lemma Fo224 : fetch_word segs (at_ base 224) = Some W_6da40.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 56 _ HCODE eq_refl). Qed.
  Lemma Fo228 : fetch_word segs (at_ base 228) = Some W_6da44.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 57 _ HCODE eq_refl). Qed.
  Lemma Fo232 : fetch_word segs (at_ base 232) = Some W_6da48.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 58 _ HCODE eq_refl). Qed.
  Lemma Fo236 : fetch_word segs (at_ base 236) = Some W_6da4c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 59 _ HCODE eq_refl). Qed.
  Lemma Fo240 : fetch_word segs (at_ base 240) = Some W_6da50.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 60 _ HCODE eq_refl). Qed.
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_6da5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_6da60.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_6da64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo264 : fetch_word segs (at_ base 264) = Some W_6da68.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 66 _ HCODE eq_refl). Qed.
  Lemma Fo268 : fetch_word segs (at_ base 268) = Some W_6da6c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 67 _ HCODE eq_refl). Qed.
  Lemma Fo272 : fetch_word segs (at_ base 272) = Some W_6da70.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 68 _ HCODE eq_refl). Qed.
  Lemma Fo276 : fetch_word segs (at_ base 276) = Some W_6da74.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 69 _ HCODE eq_refl). Qed.
  Lemma Fo280 : fetch_word segs (at_ base 280) = Some W_6da78.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 70 _ HCODE eq_refl). Qed.
  Lemma Fo284 : fetch_word segs (at_ base 284) = Some W_6da7c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 71 _ HCODE eq_refl). Qed.
  Lemma Fo288 : fetch_word segs (at_ base 288) = Some W_6da80.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 72 _ HCODE eq_refl). Qed.
  Lemma Fo292 : fetch_word segs (at_ base 292) = Some W_6da84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 73 _ HCODE eq_refl). Qed.
  Lemma Fo296 : fetch_word segs (at_ base 296) = Some W_6da88.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 74 _ HCODE eq_refl). Qed.
  Lemma Fo300 : fetch_word segs (at_ base 300) = Some W_6da8c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 75 _ HCODE eq_refl). Qed.
  Lemma Fo304 : fetch_word segs (at_ base 304) = Some W_6da90.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 76 _ HCODE eq_refl). Qed.

  Lemma Fo872 : fetch_word segs (at_ base 872) = Some W_6dcc8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 218 _ HCODE eq_refl). Qed.
  Lemma Fo876 : fetch_word segs (at_ base 876) = Some W_6dccc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 219 _ HCODE eq_refl). Qed.
  Lemma Fo880 : fetch_word segs (at_ base 880) = Some W_6dcd0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 220 _ HCODE eq_refl). Qed.
  Lemma Fo884 : fetch_word segs (at_ base 884) = Some W_6dcd4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 221 _ HCODE eq_refl). Qed.
  Lemma Fo888 : fetch_word segs (at_ base 888) = Some W_6dcd8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 222 _ HCODE eq_refl). Qed.
  Lemma Fo892 : fetch_word segs (at_ base 892) = Some W_6dcdc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 223 _ HCODE eq_refl). Qed.
  Lemma Fo896 : fetch_word segs (at_ base 896) = Some W_6dce0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 224 _ HCODE eq_refl). Qed.
  Lemma Fo900 : fetch_word segs (at_ base 900) = Some W_6dce4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 225 _ HCODE eq_refl). Qed.
  Lemma Fo904 : fetch_word segs (at_ base 904) = Some W_6dce8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 226 _ HCODE eq_refl). Qed.
  Lemma Fo908 : fetch_word segs (at_ base 908) = Some W_6dcec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 227 _ HCODE eq_refl). Qed.
  Lemma Fo912 : fetch_word segs (at_ base 912) = Some W_6dcf0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 228 _ HCODE eq_refl). Qed.
  Lemma Fo916 : fetch_word segs (at_ base 916) = Some W_6dcf4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 229 _ HCODE eq_refl). Qed.
  Lemma Fo1124 : fetch_word segs (at_ base 1124) = Some W_6ddc4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 281 _ HCODE eq_refl). Qed.
  Lemma Fo1128 : fetch_word segs (at_ base 1128) = Some W_6ddc8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 282 _ HCODE eq_refl). Qed.
  Lemma Fo1132 : fetch_word segs (at_ base 1132) = Some W_6ddcc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 283 _ HCODE eq_refl). Qed.
  Lemma Fo1136 : fetch_word segs (at_ base 1136) = Some W_6ddd0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 284 _ HCODE eq_refl). Qed.
  Lemma Fo1140 : fetch_word segs (at_ base 1140) = Some W_6ddd4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 285 _ HCODE eq_refl). Qed.
  Lemma Fo1144 : fetch_word segs (at_ base 1144) = Some W_6ddd8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 286 _ HCODE eq_refl). Qed.
  Lemma Fo1148 : fetch_word segs (at_ base 1148) = Some W_6dddc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 287 _ HCODE eq_refl). Qed.
  Lemma Fo1152 : fetch_word segs (at_ base 1152) = Some W_6dde0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 288 _ HCODE eq_refl). Qed.



  Lemma Fo1168 : fetch_word segs (at_ base 1168) = Some W_6ddf0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 292 _ HCODE eq_refl). Qed.
  Lemma Fo1172 : fetch_word segs (at_ base 1172) = Some W_6ddf4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 293 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variables ra sp : word.
  Variables fl s1s s1d : byte.
  Variables w0s w1s w0d w1d : word.

  #[local] Abbreviation U := bv_unsigned.

  Hypothesis MC : mcH segs mem dst src n bs.
  Hypothesis Hn : (1 <= n <= 64)%Z.
  Hypothesis Rg_flag : rdn segs mem (Z_to_bv 64 g_flag) 8 = Some (LE8 (Z_to_bv 64 p_flag)).
  Hypothesis Rflag : rdn segs mem (Z_to_bv 64 p_flag) 1 = Some [fl].
  Hypothesis Hfl : U fl <> 0%Z.
  Hypothesis Rrmc : rdn segs mem (Z_to_bv 64 c_rmc) 8 = Some (LE8 mcp).
  Hypothesis Rg_shoff : rdn segs mem (Z_to_bv 64 g_shoff) 8 = Some (LE8 (Z_to_bv 64 p_shoff)).
  Hypothesis Rshoff : rdn segs mem (Z_to_bv 64 p_shoff) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 80)%Z [g_flag; p_flag; c_rmc; g_shoff; p_shoff].
  Hypothesis Hsrc : (0x10007fff8000 <= U src)%Z /\ (U src + n + 8 <= 0x800000000000)%Z.
  Hypothesis Hdst : (0x10007fff8000 <= U dst)%Z /\ (U dst + n + 8 <= 0x800000000000)%Z.
  Hypothesis Rs1s : rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1s].
  Hypothesis Hs1s : (U s1s = 0 \/ (U src + n - 1) mod 8 < U s1s < 128)%Z.
  Hypothesis Rzs : forall a : word, (Sh (U src) <= U a < Sh (U src + n - 1))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0].
  Hypothesis Rw0s : rdn segs mem (Z_to_bv 64 (down8 (Sh (U src)))) 8 = Some (LE8 w0s).
  Hypothesis Rw1s : rdn segs mem (Z_to_bv 64 (down8 (Sh (U src + n - 1)))) 8 = Some (LE8 w1s).
  Hypothesis Rs1d : rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1d].
  Hypothesis Hs1d : (U s1d = 0 \/ (U dst + n - 1) mod 8 < U s1d < 128)%Z.
  Hypothesis Rzd : forall a : word, (Sh (U dst) <= U a < Sh (U dst + n - 1))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0].
  Hypothesis Rw0d : rdn segs mem (Z_to_bv 64 (down8 (Sh (U dst)))) 8 = Some (LE8 w0d).
  Hypothesis Rw1d : rdn segs mem (Z_to_bv 64 (down8 (Sh (U dst + n - 1)))) 8 = Some (LE8 w1d).
  Hypothesis Hsp : (0x10007fff8000 + 2160 <= U sp)%Z /\ (U sp < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-80)) 80 = true.
  Hypothesis Hsrc_stk : (U src + n <= U sp - 80 \/ U sp <= U src)%Z.
  Hypothesis Hdst_stk : (U dst + n <= U sp - 80 \/ U sp <= U dst)%Z.
  Hypothesis Hret : ret_ok ra.

  #[local] Abbreviation CL := (fun r => In r icpy_clob).
  #[local] Abbreviation CLX := (fun r => In r icpy_clobx).


  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.

  (* [comment removed for export] *)
  Lemma shs : (0x27fff7000 <= Sh (U src))%Z /\ (Sh (U src) <= Sh (U src + n - 1))%Z /\ (Sh (U src + n - 1) < 0x10007fff8000)%Z
              /\ (Sh (U src + n - 1) <= Sh (U src) + 8)%Z.
  Proof using Hsp Hdst Hsrc Hn sp dst base.
    pose proof (Sh_bounds (U src) ltac:(lia)). pose proof (Sh_bounds (U src + n - 1)%Z ltac:(lia)).
    pose proof (Sh_mono (U src) (U src + n - 1)%Z ltac:(lia)).
    assert (Sh (U src + n - 1) <= Sh (U src) + 8)%Z.
    { (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_le_mono (U src + n - 1) (U src + 8 * 8) 8 ltac:(lia) ltac:(lia)) as HM.
      rewrite (Z.div_add (U src) 8 8) in HM by lia. lia. }
    lia.
  Qed.


  Section WithRegs.
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = dst.
  Hypothesis H11 : getr regs 11 = src.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 n.

  Definition JM1 : word -> option byte := icpy_frame mem sp regs ra.

  Lemma JM1_out : forall x : word, (U x < U sp - 80 \/ U sp <= U x)%Z -> JM1 x = mem x.
  Proof using Hsp n src dst base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold JM1, icpy_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma JM1_low : forall x : word, (U x < U sp - 80)%Z -> JM1 x = mem x.
  Proof using Hsp n src dst base. intros x Hx. apply JM1_out. lia. Qed.


  Lemma rd_o : forall (M : word -> option byte) (B : Z) (a : word) k bs0,
    (forall x : word, (U x < B)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= B)%Z -> (B <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using Hsp Hdst Hsrc Hn sp n src dst base.
    intros M B a k bs0 HM Ha HB Hr. rewrite <- Hr. apply rdn_ext; [lia|].
    intros x Hx. apply HM. lia.
  Qed.

  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-80)) _ 80);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac addr_n := gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; rewrite ?at_addi; zlit_at;
                 try (progress ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end)); unorm).
  Ltac rd_close Hr :=
    apply (rd_o _ _ _ _ _ JM1_low);
    [ rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | lia
    | first [ exact Hr | rewrite <- Hr; f_equal; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ] ] ].
  Ltac cld F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D | addr_n; rd_close Hr | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac cldb F D bb Hr :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := bb);
        [exact F | reflexivity | exact D | addr_n; rd_close Hr]
      | step_simpl]; vn.
  Ltac cldsb F D bb Hr :=
    chain_step; [reflexivity
      | eapply step_lb with (b := bb);
        [exact F | reflexivity | exact D | addr_n; rd_close Hr]
      | step_simpl]; vn.
  Ltac gl G Hr :=
    eapply msteps_trans; [ eapply G; apply (rd_o _ _ _ _ _ JM1_low); [(lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia | lia | exact Hr] | ]; zlit_at.



  (* [comment removed for export] *)
  Section QS.
  Variable r0 : bvmap 5 word.
  Hypothesis Q11 : getr r0 11 = src.
  Hypothesis Q19 : getr r0 19 = Z_to_bv 64 (U src + n).
  #[local] Abbreviation E := (U src + n - 1)%Z.
  #[local] Abbreviation QCL := (fun x => In x [13; 14; 15; 16; 17; 19]).

  Ltac qprefix :=
    gl G116 Rg_shoff;                                                                        (* [comment removed for export] *)
    cld Fo124 D_6d9dc (Z_to_bv 64 0x7fff8000) Rshoff;                                         (* [comment removed for export] *)
    av Fo128 D_6d9e0 (Z_to_bv 64 E) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia);               (* [comment removed for export] *)
    av Fo132 D_6d9e4 (Z_to_bv 64 (Sh (U src) - 0x7fff8000)) ltac:(rewrite v_srli_3; (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end); f_equal; lia);          (* [comment removed for export] *)
    av Fo136 D_6d9e8 (Z_to_bv 64 (Sh E - 0x7fff8000)) ltac:(rewrite v_srli_3; unorm; (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end); f_equal; lia);       (* [comment removed for export] *)
    av Fo140 D_6d9ec (Z_to_bv 64 (Sh (U src))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); imm_norm; unorm; f_equal; lia);   (* [comment removed for export] *)
    av Fo144 D_6d9f0 (Z_to_bv 64 (Sh E)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); imm_norm; unorm; f_equal; lia);         (* [comment removed for export] *)
    av Fo148 D_6d9f4 (Z_to_bv 64 (down8 (Sh (U src)))) ltac:(rewrite v_andi_m8; unorm; reflexivity);     (* [comment removed for export] *)
    av Fo152 D_6d9f8 (Z_to_bv 64 (down8 (Sh E))) ltac:(rewrite v_andi_m8; unorm; reflexivity);           (* [comment removed for export] *)
    cld Fo156 D_6d9fc w0s Rw0s;                                                             (* [comment removed for export] *)
    cld Fo160 D_6da00 w1s Rw1s;                                                           (* [comment removed for export] *)
    an Fo164 D_6da04.


  End QS.



  (* [comment removed for export] *)
  Section QD.
  Variable r0 : bvmap 5 word.
  Hypothesis Q10 : getr r0 10 = dst.
  Hypothesis Q20 : getr r0 20 = Z_to_bv 64 (U dst + n).
  #[local] Abbreviation E := (U dst + n - 1)%Z.
  #[local] Abbreviation QCL := (fun x => In x [13; 14; 15; 16; 17; 20]).

  Ltac qprefix :=
    gl G188 Rg_shoff;                                                                        (* [comment removed for export] *)
    cld Fo196 D_6da24 (Z_to_bv 64 0x7fff8000) Rshoff;                                         (* [comment removed for export] *)
    av Fo200 D_6da28 (Z_to_bv 64 E) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia);               (* [comment removed for export] *)
    av Fo204 D_6da2c (Z_to_bv 64 (Sh (U dst) - 0x7fff8000)) ltac:(rewrite v_srli_3; (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end); f_equal; lia);          (* [comment removed for export] *)
    av Fo208 D_6da30 (Z_to_bv 64 (Sh E - 0x7fff8000)) ltac:(rewrite v_srli_3; unorm; (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end); f_equal; lia);       (* [comment removed for export] *)
    av Fo212 D_6da34 (Z_to_bv 64 (Sh (U dst))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); imm_norm; unorm; f_equal; lia);   (* [comment removed for export] *)
    av Fo216 D_6da38 (Z_to_bv 64 (Sh E)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); imm_norm; unorm; f_equal; lia);         (* [comment removed for export] *)
    av Fo220 D_6da3c (Z_to_bv 64 (down8 (Sh (U dst)))) ltac:(rewrite v_andi_m8; unorm; reflexivity);     (* [comment removed for export] *)
    av Fo224 D_6da40 (Z_to_bv 64 (down8 (Sh E))) ltac:(rewrite v_andi_m8; unorm; reflexivity);           (* [comment removed for export] *)
    cld Fo228 D_6da44 w0d Rw0d;                                                             (* [comment removed for export] *)
    cld Fo232 D_6da48 w1d Rw1d;                                                           (* [comment removed for export] *)
    an Fo236 D_6da4c.


  End QD.









  End WithRegs.
End ICPS.

End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
