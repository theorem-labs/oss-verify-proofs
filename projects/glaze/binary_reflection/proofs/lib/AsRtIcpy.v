(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
(* [comment removed for export] *)
Local Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac nodisjk K := repeat match goal with H : _ \/ _ |- _ => tryif constr_eq H K then fail else clear H end.

Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Definition icpy_words : list (option (bv 32)) :=
  [
   Some W_6d960; Some W_6d964; Some W_6d968; Some W_6d96c; Some W_6d970; Some W_6d974; Some W_6d978; Some
   W_6d97c; Some W_6d980; Some W_6d984; Some W_6d988; Some W_6d98c; Some W_6d990; None; None; Some W_6d99c; Some
   W_6d9a0; Some W_6d9a4; Some W_6d9a8; Some W_6d9ac; Some W_6d9b0; Some W_6d9b4; Some W_6d9b8; Some W_6d9bc;
   Some W_6d9c0; Some W_6d9c4; Some W_6d9c8; Some W_6d9cc; Some W_6d9d0; None; None; Some W_6d9dc; Some W_6d9e0;
   Some W_6d9e4; Some W_6d9e8; Some W_6d9ec; Some W_6d9f0; Some W_6d9f4; Some W_6d9f8; Some W_6d9fc; Some
   W_6da00; Some W_6da04; Some W_6da08; Some W_6da0c; Some W_6da10; Some W_6da14; Some W_6da18; None; None; Some
   W_6da24; Some W_6da28; Some W_6da2c; Some W_6da30; Some W_6da34; Some W_6da38; Some W_6da3c; Some W_6da40;
   Some W_6da44; Some W_6da48; Some W_6da4c; Some W_6da50; None; None; Some W_6da5c; Some W_6da60; Some W_6da64;
   Some W_6da68; Some W_6da6c; Some W_6da70; Some W_6da74; Some W_6da78; Some W_6da7c; Some W_6da80; Some
   W_6da84; Some W_6da88; Some W_6da8c; Some W_6da90; Some W_6da94; Some W_6da98; Some W_6da9c; Some W_6daa0;
   Some W_6daa4; Some W_6daa8; Some W_6daac; Some W_6dab0; Some W_6dab4; Some W_6dab8; Some W_6dabc; Some
   W_6dac0; Some W_6dac4; Some W_6dac8; Some W_6dacc; Some W_6dad0; Some W_6dad4; Some W_6dad8; Some W_6dadc;
   Some W_6dae0; Some W_6dae4; Some W_6dae8; Some W_6daec; Some W_6daf0; Some W_6daf4; Some W_6daf8; Some
   W_6dafc; Some W_6db00; Some W_6db04; Some W_6db08; Some W_6db0c; Some W_6db10; Some W_6db14; Some W_6db18;
   Some W_6db1c; None; None; Some W_6db28; Some W_6db2c; Some W_6db30; Some W_6db34; Some W_6db38; Some W_6db3c;
   Some W_6db40; Some W_6db44; Some W_6db48; Some W_6db4c; Some W_6db50; Some W_6db54; Some W_6db58; Some
   W_6db5c; Some W_6db60; Some W_6db64; Some W_6db68; Some W_6db6c; Some W_6db70; Some W_6db74; Some W_6db78;
   Some W_6db7c; Some W_6db80; Some W_6db84; Some W_6db88; Some W_6db8c; Some W_6db90; Some W_6db94; Some
   W_6db98; Some W_6db9c; Some W_6dba0; Some W_6dba4; Some W_6dba8; None; None; Some W_6dbb4; Some W_6dbb8; Some
   W_6dbbc; Some W_6dbc0; Some W_6dbc4; Some W_6dbc8; Some W_6dbcc; Some W_6dbd0; Some W_6dbd4; None; Some
   W_6dbdc; Some W_6dbe0; Some W_6dbe4; Some W_6dbe8; Some W_6dbec; Some W_6dbf0; Some W_6dbf4; Some W_6dbf8;
   Some W_6dbfc; None; Some W_6dc04; Some W_6dc08; Some W_6dc0c; Some W_6dc10; Some W_6dc14; Some W_6dc18; Some
   W_6dc1c; Some W_6dc20; Some W_6dc24; Some W_6dc28; Some W_6dc2c; Some W_6dc30; Some W_6dc34; Some W_6dc38;
   Some W_6dc3c; Some W_6dc40; Some W_6dc44; Some W_6dc48; Some W_6dc4c; Some W_6dc50; Some W_6dc54; Some
   W_6dc58; Some W_6dc5c; Some W_6dc60; Some W_6dc64; None; None; Some W_6dc70; Some W_6dc74; Some W_6dc78; Some
   W_6dc7c; Some W_6dc80; Some W_6dc84; Some W_6dc88; Some W_6dc8c; Some W_6dc90; Some W_6dc94; Some W_6dc98;
   Some W_6dc9c; Some W_6dca0; Some W_6dca4; Some W_6dca8; Some W_6dcac; Some W_6dcb0; Some W_6dcb4; Some
   W_6dcb8; Some W_6dcbc; Some W_6dcc0; Some W_6dcc4; Some W_6dcc8; Some W_6dccc; Some W_6dcd0; Some W_6dcd4;
   Some W_6dcd8; Some W_6dcdc; Some W_6dce0; Some W_6dce4; Some W_6dce8; Some W_6dcec; Some W_6dcf0; Some
   W_6dcf4; Some W_6dcf8; Some W_6dcfc; Some W_6dd00; Some W_6dd04; Some W_6dd08; Some W_6dd0c; Some W_6dd10;
   Some W_6dd14; Some W_6dd18; Some W_6dd1c; Some W_6dd20; Some W_6dd24; None; Some W_6dd2c; Some W_6dd30; Some
   W_6dd34; Some W_6dd38; Some W_6dd3c; Some W_6dd40; Some W_6dd44; Some W_6dd48; Some W_6dd4c; Some W_6dd50;
   Some W_6dd54; Some W_6dd58; Some W_6dd5c; Some W_6dd60; Some W_6dd64; Some W_6dd68; Some W_6dd6c; Some
   W_6dd70; None; None; Some W_6dd7c; Some W_6dd80; Some W_6dd84; Some W_6dd88; Some W_6dd8c; Some W_6dd90; Some
   W_6dd94; Some W_6dd98; Some W_6dd9c; Some W_6dda0; Some W_6dda4; Some W_6dda8; Some W_6ddac; Some W_6ddb0;
   Some W_6ddb4; Some W_6ddb8; Some W_6ddbc; Some W_6ddc0; Some W_6ddc4; Some W_6ddc8; Some W_6ddcc; Some
   W_6ddd0; Some W_6ddd4; Some W_6ddd8; Some W_6dddc; Some W_6dde0; Some W_6dde4; Some W_6dde8; Some W_6ddec;
   Some W_6ddf0; Some W_6ddf4; Some W_6ddf8; Some W_6ddfc; Some W_6de00; Some W_6de04; Some W_6de08; Some
   W_6de0c; Some W_6de10; Some W_6de14; Some W_6de18; Some W_6de1c; Some W_6de20; None
  ]%list.


(* [comment removed for export] *)
Definition icpy_clob : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].
Definition icpy_clobx : list reg := [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Record icpy_tab : Type := ICPT { it_base : word; it_rip : rip_tab; it_mcp : word; it_g_flag : Z; it_p_flag : Z; it_c_rmc : Z }.

Record icpy_tab_ok (segs : list Segment) (t : icpy_tab) : Prop := ICPTOK {
  ito_code : code_ato segs (it_base t) 0 icpy_words;
  ito_rip : rip_tab_ok segs (it_rip t);
  ito_rip_base : rt_base (it_rip t) = at_ (it_base t) 9776;
  ito_mcp : code_at segs (it_mcp t) 0 mmemcpy_words;
  ito_g52 : gload segs (it_base t) 52 13 (it_g_flag t);
  ito_g244 : gload segs (it_base t) 244 13 (it_c_rmc t);
  ito_base : (bv_unsigned (it_base t) mod 2 = 0)%Z /\ (bv_unsigned (it_base t) + 20000 < 2 ^ 64)%Z;
  ito_mcp_ok : ret_ok (it_mcp t) }.

(* [comment removed for export] *)
Definition icpy_frame (mem : word -> option byte) (sp : word) (regs : bvmap 5 word) (ra : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (word_to_le_bytes 8 ra))
    (at_ sp (-16)) (word_to_le_bytes 8 (getr regs 8)))
    (at_ sp (-24)) (word_to_le_bytes 8 (getr regs 9)))
    (at_ sp (-32)) (word_to_le_bytes 8 (getr regs 18)))
    (at_ sp (-40)) (word_to_le_bytes 8 (getr regs 19)))
    (at_ sp (-48)) (word_to_le_bytes 8 (getr regs 20)))
    (at_ sp (-56)) (word_to_le_bytes 8 (getr regs 21)))
    (at_ sp (-64)) (word_to_le_bytes 8 (getr regs 22)))
    (at_ sp (-72)) (word_to_le_bytes 8 (getr regs 23)))
    (at_ sp (-80)) (word_to_le_bytes 8 (getr regs 24)).


(* [comment removed for export] *)
Record icpyH (segs : list Segment) (t : icpy_tab) (mem : word -> option byte)
       (dst src : word) (n : Z) (bs : list byte) (ra sp : word) (fl : byte)
       (s0s s1s s0d s1d : byte) (midend : word) : Prop := ICPYH {
  ih_mc : mcH segs mem dst src n bs;
  ih_n : (65 <= n <= 2 ^ 43)%Z;
  ih_g_flag : rdn segs mem (Z_to_bv 64 (it_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (it_p_flag t)));
  ih_flag : rdn segs mem (Z_to_bv 64 (it_p_flag t)) 1 = Some [fl];
  ih_fl : bv_unsigned fl <> 0%Z;
  ih_rmc : rdn segs mem (Z_to_bv 64 (it_c_rmc t)) 8 = Some (word_to_le_bytes 8 (it_mcp t));
  ih_cellsH : m2sH segs (rt_m2s (it_rip t)) mem src midend;   (* [comment removed for export] *)
  ih_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 2240)%Z
               (it_g_flag t :: it_p_flag t :: it_c_rmc t :: m2s_cells (rt_m2s (it_rip t)));
  ih_src : (0x10007fff8000 <= bv_unsigned src)%Z /\ (bv_unsigned src + n + 8 <= 0x800000000000)%Z;
  ih_dst : (0x10007fff8000 <= bv_unsigned dst)%Z /\ (bv_unsigned dst + n + 8 <= 0x800000000000)%Z;
  (* [comment removed for export] *)
  ih_s0s : rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned src))) 1 = Some [s0s];
  ih_s0sok : (bv_unsigned s0s = 0 \/ bv_unsigned src mod 8 < bv_unsigned s0s < 128)%Z;
  ih_s1s : rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned src + n - 1))) 1 = Some [s1s];
  ih_s1sok : (bv_unsigned s1s = 0 \/ (bv_unsigned src + n - 1) mod 8 < bv_unsigned s1s < 128)%Z;
  ih_zs : forall a : word, (Sh (up8 (bv_unsigned src)) <= bv_unsigned a < Sh (down8 (bv_unsigned src + n)))%Z ->
            rdn segs mem a 1 = Some [Z_to_bv 8 0];
  (* [comment removed for export] *)
  ih_s0d : rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned dst))) 1 = Some [s0d];
  ih_s0dok : (bv_unsigned s0d = 0 \/ bv_unsigned dst mod 8 < bv_unsigned s0d < 128)%Z;
  ih_s1d : rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned dst + n - 1))) 1 = Some [s1d];
  ih_s1dok : (bv_unsigned s1d = 0 \/ (bv_unsigned dst + n - 1) mod 8 < bv_unsigned s1d < 128)%Z;
  ih_zd : forall a : word, (Sh (up8 (bv_unsigned dst)) <= bv_unsigned a < Sh (down8 (bv_unsigned dst + n)))%Z ->
            rdn segs mem a 1 = Some [Z_to_bv 8 0];
  (* [comment removed for export] *)
  ih_sp : (0x10007fff8000 + 2240 <= bv_unsigned sp)%Z /\ (bv_unsigned sp < 2 ^ 64)%Z;
  ih_stk : store_ok segs mem (at_ sp (-2240)) 2240 = true;
  ih_src_stk : (bv_unsigned src + n <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= bv_unsigned src)%Z;
  ih_dst_stk : (bv_unsigned dst + n <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= bv_unsigned dst)%Z;
  ih_ret : ret_ok ra }.

Section ICPY.
  Variable segs : list Segment.
  Variable base : word.
  Variable rt : rip_tab.
  Variable mcp : word.
  Variables g_flag p_flag c_rmc : Z.
  Hypothesis HCODE : code_ato segs base 0 icpy_words.
  Hypothesis RTOK : rip_tab_ok segs rt.
  Hypothesis RTB : rt_base rt = at_ base 9776.
  Hypothesis MCP : code_at segs mcp 0 mmemcpy_words.
  Hypothesis G52 : gload segs base 52 13 g_flag.
  Hypothesis G244 : gload segs base 244 13 c_rmc.
  Hypothesis Hbase : (bv_unsigned base mod 2 = 0)%Z /\ (bv_unsigned base + 20000 < 2 ^ 64)%Z.

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
  Lemma Fo308 : fetch_word segs (at_ base 308) = Some W_6da94.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 77 _ HCODE eq_refl). Qed.









  Lemma Fo348 : fetch_word segs (at_ base 348) = Some W_6dabc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 87 _ HCODE eq_refl). Qed.

  Lemma Fo356 : fetch_word segs (at_ base 356) = Some W_6dac4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 89 _ HCODE eq_refl). Qed.

  Lemma Fo364 : fetch_word segs (at_ base 364) = Some W_6dacc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 91 _ HCODE eq_refl). Qed.



  Lemma Fo380 : fetch_word segs (at_ base 380) = Some W_6dadc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 95 _ HCODE eq_refl). Qed.
  Lemma Fo384 : fetch_word segs (at_ base 384) = Some W_6dae0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 96 _ HCODE eq_refl). Qed.
  Lemma Fo388 : fetch_word segs (at_ base 388) = Some W_6dae4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 97 _ HCODE eq_refl). Qed.

  Lemma Fo396 : fetch_word segs (at_ base 396) = Some W_6daec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 99 _ HCODE eq_refl). Qed.
  Lemma Fo400 : fetch_word segs (at_ base 400) = Some W_6daf0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 100 _ HCODE eq_refl). Qed.
  Lemma Fo404 : fetch_word segs (at_ base 404) = Some W_6daf4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 101 _ HCODE eq_refl). Qed.
  Lemma Fo408 : fetch_word segs (at_ base 408) = Some W_6daf8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 102 _ HCODE eq_refl). Qed.
  Lemma Fo412 : fetch_word segs (at_ base 412) = Some W_6dafc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 103 _ HCODE eq_refl). Qed.
  Lemma Fo416 : fetch_word segs (at_ base 416) = Some W_6db00.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 104 _ HCODE eq_refl). Qed.
  Lemma Fo420 : fetch_word segs (at_ base 420) = Some W_6db04.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 105 _ HCODE eq_refl). Qed.
  Lemma Fo424 : fetch_word segs (at_ base 424) = Some W_6db08.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 106 _ HCODE eq_refl). Qed.
  Lemma Fo428 : fetch_word segs (at_ base 428) = Some W_6db0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 107 _ HCODE eq_refl). Qed.
  Lemma Fo432 : fetch_word segs (at_ base 432) = Some W_6db10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 108 _ HCODE eq_refl). Qed.
  Lemma Fo436 : fetch_word segs (at_ base 436) = Some W_6db14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 109 _ HCODE eq_refl). Qed.
  Lemma Fo440 : fetch_word segs (at_ base 440) = Some W_6db18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 110 _ HCODE eq_refl). Qed.
  Lemma Fo444 : fetch_word segs (at_ base 444) = Some W_6db1c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 111 _ HCODE eq_refl). Qed.
  Lemma Fo456 : fetch_word segs (at_ base 456) = Some W_6db28.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 114 _ HCODE eq_refl). Qed.
  Lemma Fo460 : fetch_word segs (at_ base 460) = Some W_6db2c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 115 _ HCODE eq_refl). Qed.
  Lemma Fo464 : fetch_word segs (at_ base 464) = Some W_6db30.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 116 _ HCODE eq_refl). Qed.
  Lemma Fo468 : fetch_word segs (at_ base 468) = Some W_6db34.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 117 _ HCODE eq_refl). Qed.
  Lemma Fo472 : fetch_word segs (at_ base 472) = Some W_6db38.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 118 _ HCODE eq_refl). Qed.
  Lemma Fo476 : fetch_word segs (at_ base 476) = Some W_6db3c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 119 _ HCODE eq_refl). Qed.
  Lemma Fo480 : fetch_word segs (at_ base 480) = Some W_6db40.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 120 _ HCODE eq_refl). Qed.
  Lemma Fo484 : fetch_word segs (at_ base 484) = Some W_6db44.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 121 _ HCODE eq_refl). Qed.
  Lemma Fo488 : fetch_word segs (at_ base 488) = Some W_6db48.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 122 _ HCODE eq_refl). Qed.
  Lemma Fo492 : fetch_word segs (at_ base 492) = Some W_6db4c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 123 _ HCODE eq_refl). Qed.
  Lemma Fo496 : fetch_word segs (at_ base 496) = Some W_6db50.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 124 _ HCODE eq_refl). Qed.
  Lemma Fo500 : fetch_word segs (at_ base 500) = Some W_6db54.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 125 _ HCODE eq_refl). Qed.
  Lemma Fo504 : fetch_word segs (at_ base 504) = Some W_6db58.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 126 _ HCODE eq_refl). Qed.
  Lemma Fo508 : fetch_word segs (at_ base 508) = Some W_6db5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 127 _ HCODE eq_refl). Qed.
  Lemma Fo512 : fetch_word segs (at_ base 512) = Some W_6db60.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 128 _ HCODE eq_refl). Qed.
  Lemma Fo516 : fetch_word segs (at_ base 516) = Some W_6db64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 129 _ HCODE eq_refl). Qed.
  Lemma Fo520 : fetch_word segs (at_ base 520) = Some W_6db68.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 130 _ HCODE eq_refl). Qed.

  Lemma Fo528 : fetch_word segs (at_ base 528) = Some W_6db70.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 132 _ HCODE eq_refl). Qed.
  Lemma Fo532 : fetch_word segs (at_ base 532) = Some W_6db74.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 133 _ HCODE eq_refl). Qed.



  Lemma Fo548 : fetch_word segs (at_ base 548) = Some W_6db84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 137 _ HCODE eq_refl). Qed.
  Lemma Fo552 : fetch_word segs (at_ base 552) = Some W_6db88.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 138 _ HCODE eq_refl). Qed.
  Lemma Fo556 : fetch_word segs (at_ base 556) = Some W_6db8c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 139 _ HCODE eq_refl). Qed.
  Lemma Fo560 : fetch_word segs (at_ base 560) = Some W_6db90.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 140 _ HCODE eq_refl). Qed.









  Lemma Fo608 : fetch_word segs (at_ base 608) = Some W_6dbc0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 152 _ HCODE eq_refl). Qed.
  Lemma Fo612 : fetch_word segs (at_ base 612) = Some W_6dbc4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 153 _ HCODE eq_refl). Qed.
  Lemma Fo616 : fetch_word segs (at_ base 616) = Some W_6dbc8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 154 _ HCODE eq_refl). Qed.
  Lemma Fo620 : fetch_word segs (at_ base 620) = Some W_6dbcc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 155 _ HCODE eq_refl). Qed.
  Lemma Fo624 : fetch_word segs (at_ base 624) = Some W_6dbd0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 156 _ HCODE eq_refl). Qed.
  Lemma Fo628 : fetch_word segs (at_ base 628) = Some W_6dbd4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 157 _ HCODE eq_refl). Qed.
  Lemma Fo636 : fetch_word segs (at_ base 636) = Some W_6dbdc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 159 _ HCODE eq_refl). Qed.
  Lemma Fo640 : fetch_word segs (at_ base 640) = Some W_6dbe0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 160 _ HCODE eq_refl). Qed.
  Lemma Fo644 : fetch_word segs (at_ base 644) = Some W_6dbe4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 161 _ HCODE eq_refl). Qed.
  Lemma Fo648 : fetch_word segs (at_ base 648) = Some W_6dbe8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 162 _ HCODE eq_refl). Qed.
  Lemma Fo652 : fetch_word segs (at_ base 652) = Some W_6dbec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 163 _ HCODE eq_refl). Qed.
  Lemma Fo656 : fetch_word segs (at_ base 656) = Some W_6dbf0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 164 _ HCODE eq_refl). Qed.

















  Lemma Fo732 : fetch_word segs (at_ base 732) = Some W_6dc3c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 183 _ HCODE eq_refl). Qed.
  Lemma Fo736 : fetch_word segs (at_ base 736) = Some W_6dc40.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 184 _ HCODE eq_refl). Qed.
  Lemma Fo740 : fetch_word segs (at_ base 740) = Some W_6dc44.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 185 _ HCODE eq_refl). Qed.
  Lemma Fo744 : fetch_word segs (at_ base 744) = Some W_6dc48.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 186 _ HCODE eq_refl). Qed.
  Lemma Fo748 : fetch_word segs (at_ base 748) = Some W_6dc4c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 187 _ HCODE eq_refl). Qed.
  Lemma Fo752 : fetch_word segs (at_ base 752) = Some W_6dc50.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 188 _ HCODE eq_refl). Qed.
  Lemma Fo756 : fetch_word segs (at_ base 756) = Some W_6dc54.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 189 _ HCODE eq_refl). Qed.
  Lemma Fo760 : fetch_word segs (at_ base 760) = Some W_6dc58.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 190 _ HCODE eq_refl). Qed.
  Lemma Fo764 : fetch_word segs (at_ base 764) = Some W_6dc5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 191 _ HCODE eq_refl). Qed.
  Lemma Fo768 : fetch_word segs (at_ base 768) = Some W_6dc60.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 192 _ HCODE eq_refl). Qed.
  Lemma Fo772 : fetch_word segs (at_ base 772) = Some W_6dc64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 193 _ HCODE eq_refl). Qed.
  Lemma Fo784 : fetch_word segs (at_ base 784) = Some W_6dc70.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 196 _ HCODE eq_refl). Qed.
  Lemma Fo788 : fetch_word segs (at_ base 788) = Some W_6dc74.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 197 _ HCODE eq_refl). Qed.
  Lemma Fo792 : fetch_word segs (at_ base 792) = Some W_6dc78.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 198 _ HCODE eq_refl). Qed.
  Lemma Fo796 : fetch_word segs (at_ base 796) = Some W_6dc7c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 199 _ HCODE eq_refl). Qed.
  Lemma Fo800 : fetch_word segs (at_ base 800) = Some W_6dc80.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 200 _ HCODE eq_refl). Qed.
  Lemma Fo804 : fetch_word segs (at_ base 804) = Some W_6dc84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 201 _ HCODE eq_refl). Qed.
  Lemma Fo808 : fetch_word segs (at_ base 808) = Some W_6dc88.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 202 _ HCODE eq_refl). Qed.









  Lemma Fo848 : fetch_word segs (at_ base 848) = Some W_6dcb0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 212 _ HCODE eq_refl). Qed.
  Lemma Fo852 : fetch_word segs (at_ base 852) = Some W_6dcb4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 213 _ HCODE eq_refl). Qed.

  Lemma Fo860 : fetch_word segs (at_ base 860) = Some W_6dcbc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 215 _ HCODE eq_refl). Qed.
  Lemma Fo864 : fetch_word segs (at_ base 864) = Some W_6dcc0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 216 _ HCODE eq_refl). Qed.

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
  Lemma Fo920 : fetch_word segs (at_ base 920) = Some W_6dcf8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 230 _ HCODE eq_refl). Qed.
  Lemma Fo924 : fetch_word segs (at_ base 924) = Some W_6dcfc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 231 _ HCODE eq_refl). Qed.
  Lemma Fo928 : fetch_word segs (at_ base 928) = Some W_6dd00.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 232 _ HCODE eq_refl). Qed.
  Lemma Fo932 : fetch_word segs (at_ base 932) = Some W_6dd04.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 233 _ HCODE eq_refl). Qed.
  Lemma Fo936 : fetch_word segs (at_ base 936) = Some W_6dd08.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 234 _ HCODE eq_refl). Qed.
  Lemma Fo940 : fetch_word segs (at_ base 940) = Some W_6dd0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 235 _ HCODE eq_refl). Qed.
  Lemma Fo944 : fetch_word segs (at_ base 944) = Some W_6dd10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 236 _ HCODE eq_refl). Qed.
  Lemma Fo948 : fetch_word segs (at_ base 948) = Some W_6dd14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 237 _ HCODE eq_refl). Qed.
  Lemma Fo952 : fetch_word segs (at_ base 952) = Some W_6dd18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 238 _ HCODE eq_refl). Qed.
  Lemma Fo956 : fetch_word segs (at_ base 956) = Some W_6dd1c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 239 _ HCODE eq_refl). Qed.
  Lemma Fo960 : fetch_word segs (at_ base 960) = Some W_6dd20.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 240 _ HCODE eq_refl). Qed.
  Lemma Fo964 : fetch_word segs (at_ base 964) = Some W_6dd24.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 241 _ HCODE eq_refl). Qed.
  Lemma Fo972 : fetch_word segs (at_ base 972) = Some W_6dd2c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 243 _ HCODE eq_refl). Qed.
  Lemma Fo976 : fetch_word segs (at_ base 976) = Some W_6dd30.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 244 _ HCODE eq_refl). Qed.
  Lemma Fo980 : fetch_word segs (at_ base 980) = Some W_6dd34.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 245 _ HCODE eq_refl). Qed.
  Lemma Fo984 : fetch_word segs (at_ base 984) = Some W_6dd38.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 246 _ HCODE eq_refl). Qed.
  Lemma Fo988 : fetch_word segs (at_ base 988) = Some W_6dd3c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 247 _ HCODE eq_refl). Qed.
  Lemma Fo992 : fetch_word segs (at_ base 992) = Some W_6dd40.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 248 _ HCODE eq_refl). Qed.
  Lemma Fo996 : fetch_word segs (at_ base 996) = Some W_6dd44.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 249 _ HCODE eq_refl). Qed.
  Lemma Fo1000 : fetch_word segs (at_ base 1000) = Some W_6dd48.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 250 _ HCODE eq_refl). Qed.
  Lemma Fo1004 : fetch_word segs (at_ base 1004) = Some W_6dd4c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 251 _ HCODE eq_refl). Qed.

  Lemma Fo1012 : fetch_word segs (at_ base 1012) = Some W_6dd54.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 253 _ HCODE eq_refl). Qed.
  Lemma Fo1016 : fetch_word segs (at_ base 1016) = Some W_6dd58.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 254 _ HCODE eq_refl). Qed.
  Lemma Fo1020 : fetch_word segs (at_ base 1020) = Some W_6dd5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 255 _ HCODE eq_refl). Qed.

  Lemma Fo1028 : fetch_word segs (at_ base 1028) = Some W_6dd64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 257 _ HCODE eq_refl). Qed.
  Lemma Fo1032 : fetch_word segs (at_ base 1032) = Some W_6dd68.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 258 _ HCODE eq_refl). Qed.
  Lemma Fo1036 : fetch_word segs (at_ base 1036) = Some W_6dd6c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 259 _ HCODE eq_refl). Qed.
  Lemma Fo1040 : fetch_word segs (at_ base 1040) = Some W_6dd70.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 260 _ HCODE eq_refl). Qed.
  Lemma Fo1052 : fetch_word segs (at_ base 1052) = Some W_6dd7c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 263 _ HCODE eq_refl). Qed.
  Lemma Fo1056 : fetch_word segs (at_ base 1056) = Some W_6dd80.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 264 _ HCODE eq_refl). Qed.
  Lemma Fo1060 : fetch_word segs (at_ base 1060) = Some W_6dd84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 265 _ HCODE eq_refl). Qed.
  Lemma Fo1064 : fetch_word segs (at_ base 1064) = Some W_6dd88.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 266 _ HCODE eq_refl). Qed.

  Lemma Fo1072 : fetch_word segs (at_ base 1072) = Some W_6dd90.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 268 _ HCODE eq_refl). Qed.
  Lemma Fo1076 : fetch_word segs (at_ base 1076) = Some W_6dd94.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 269 _ HCODE eq_refl). Qed.
  Lemma Fo1080 : fetch_word segs (at_ base 1080) = Some W_6dd98.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 270 _ HCODE eq_refl). Qed.
  Lemma Fo1084 : fetch_word segs (at_ base 1084) = Some W_6dd9c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 271 _ HCODE eq_refl). Qed.
  Lemma Fo1088 : fetch_word segs (at_ base 1088) = Some W_6dda0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 272 _ HCODE eq_refl). Qed.
  Lemma Fo1092 : fetch_word segs (at_ base 1092) = Some W_6dda4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 273 _ HCODE eq_refl). Qed.
  Lemma Fo1096 : fetch_word segs (at_ base 1096) = Some W_6dda8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 274 _ HCODE eq_refl). Qed.
  Lemma Fo1100 : fetch_word segs (at_ base 1100) = Some W_6ddac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 275 _ HCODE eq_refl). Qed.
  Lemma Fo1104 : fetch_word segs (at_ base 1104) = Some W_6ddb0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 276 _ HCODE eq_refl). Qed.
  Lemma Fo1108 : fetch_word segs (at_ base 1108) = Some W_6ddb4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 277 _ HCODE eq_refl). Qed.



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
  Lemma Fo1176 : fetch_word segs (at_ base 1176) = Some W_6ddf8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 294 _ HCODE eq_refl). Qed.
  Lemma Fo1180 : fetch_word segs (at_ base 1180) = Some W_6ddfc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 295 _ HCODE eq_refl). Qed.
  Lemma Fo1184 : fetch_word segs (at_ base 1184) = Some W_6de00.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 296 _ HCODE eq_refl). Qed.
  Lemma Fo1188 : fetch_word segs (at_ base 1188) = Some W_6de04.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 297 _ HCODE eq_refl). Qed.
  Lemma Fo1192 : fetch_word segs (at_ base 1192) = Some W_6de08.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 298 _ HCODE eq_refl). Qed.
  Lemma Fo1196 : fetch_word segs (at_ base 1196) = Some W_6de0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 299 _ HCODE eq_refl). Qed.
  Lemma Fo1200 : fetch_word segs (at_ base 1200) = Some W_6de10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 300 _ HCODE eq_refl). Qed.
  Lemma Fo1204 : fetch_word segs (at_ base 1204) = Some W_6de14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 301 _ HCODE eq_refl). Qed.
  Lemma Fo1208 : fetch_word segs (at_ base 1208) = Some W_6de18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 302 _ HCODE eq_refl). Qed.
  Lemma Fo1212 : fetch_word segs (at_ base 1212) = Some W_6de1c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 303 _ HCODE eq_refl). Qed.
  Lemma Fo1216 : fetch_word segs (at_ base 1216) = Some W_6de20.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 icpy_words 304 _ HCODE eq_refl). Qed.


  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variables ra sp : word.
  Variables fl s0s s1s s0d s1d : byte.
  Variable midend : word.

  #[local] Abbreviation U := bv_unsigned.
  #[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

  Hypothesis MC : mcH segs mem dst src n bs.
  Hypothesis Hn : (65 <= n <= 2 ^ 43)%Z.
  Hypothesis Rg_flag : rdn segs mem (Z_to_bv 64 g_flag) 8 = Some (LE8 p_flag).
  Hypothesis Rflag : rdn segs mem (Z_to_bv 64 p_flag) 1 = Some [fl].
  Hypothesis Hfl : U fl <> 0%Z.
  Hypothesis Rrmc : rdn segs mem (Z_to_bv 64 c_rmc) 8 = Some (word_to_le_bytes 8 mcp).
  Hypothesis CH : m2sH segs (rt_m2s rt) mem src midend.
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 2240)%Z (g_flag :: p_flag :: c_rmc :: m2s_cells (rt_m2s rt)).
  Hypothesis Hsrc : (0x10007fff8000 <= U src)%Z /\ (U src + n + 8 <= 0x800000000000)%Z.
  Hypothesis Hdst : (0x10007fff8000 <= U dst)%Z /\ (U dst + n + 8 <= 0x800000000000)%Z.
  Hypothesis Rs0s : rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0s].
  Hypothesis Hs0s : (U s0s = 0 \/ U src mod 8 < U s0s < 128)%Z.
  Hypothesis Rs1s : rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1s].
  Hypothesis Hs1s : (U s1s = 0 \/ (U src + n - 1) mod 8 < U s1s < 128)%Z.
  Hypothesis Rzs : forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0].
  Hypothesis Rs0d : rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0d].
  Hypothesis Hs0d : (U s0d = 0 \/ U dst mod 8 < U s0d < 128)%Z.
  Hypothesis Rs1d : rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1d].
  Hypothesis Hs1d : (U s1d = 0 \/ (U dst + n - 1) mod 8 < U s1d < 128)%Z.
  Hypothesis Rzd : forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0].
  Hypothesis Hsp : (0x10007fff8000 + 2240 <= U sp)%Z /\ (U sp < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-2240)) 2240 = true.
  Hypothesis Hsrc_stk : (U src + n <= U sp - 2240 \/ U sp <= U src)%Z.
  Hypothesis Hdst_stk : (U dst + n <= U sp - 2240 \/ U sp <= U dst)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hmcp : ret_ok mcp.

  #[local] Abbreviation CL := (fun r => In r icpy_clob).
  #[local] Abbreviation CLX := (fun r => In r icpy_clobx).

  Section WithRegs.
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = dst.
  Hypothesis H11 : getr regs 11 = src.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 n.

  Definition IM1 : word -> option byte := icpy_frame mem sp regs ra.

  Lemma IM1_outside : forall x : word, (U x < U sp - 80 \/ U sp <= U x)%Z -> IM1 x = mem x.
  Proof using Hsp n src dst base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold IM1, icpy_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_out : forall (M : word -> option byte) (a : word) k bs0,
    (forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= U sp - 2240 \/ U sp <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using Hsp Hdst Hsrc Hn n src dst base.
    intros M a k bs0 HM Ha Hnw Hr. rewrite <- Hr. apply rdn_ext; [exact Hnw|].
    intros x Hx. apply HM. lia.
  Qed.

  Lemma rd_outZ : forall (M : word -> option byte) (c : Z) k bs0,
    (forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= U sp - 2240)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs0 -> rdn segs M (Z_to_bv 64 c) k = Some bs0.
  Proof using Hsp Hdst Hsrc Hn n src dst base.
    intros M c k bs0 HM Hc Hk Hr. pose proof (u64_range sp). apply (rd_out M); try assumption; wd_ulia.
  Qed.

  Lemma IM1_agree : forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> IM1 x = mem x.
  Proof using Hsp n src dst base. intros x Hx. apply IM1_outside. lia. Qed.


  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold m2s_cells in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.

  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-2240)) _ 2240);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac gl G Hr :=
    eapply msteps_trans; [ eapply G; apply (rd_out IM1 _ _ _ IM1_agree); [(lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | exact Hr] | ]; zlit_at.


  (* [comment removed for export] *)
  (* [comment removed for export] *) Ltac rdo HMx Hr := apply (rd_outZ _ _ _ _ HMx); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr].
  Lemma ripH_on : forall (M : word -> option byte) (beg : word) (raX : word) (s0 s1 : byte),
    (forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (0x10007fff8000 <= U beg)%Z -> (U beg + n + 8 <= 0x800000000000)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U beg))) 1 = Some [s0] -> (U s0 = 0 \/ U beg mod 8 < U s0 < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U beg + n - 1))) 1 = Some [s1] -> (U s1 = 0 \/ (U beg + n - 1) mod 8 < U s1 < 128)%Z ->
    (forall a : word, (Sh (up8 (U beg)) <= U a < Sh (down8 (U beg + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok raX ->
    ripH segs rt M beg (Z_to_bv 64 n) raX (at_ sp (-2160)) s0 s1 midend.
  Proof using Hstk Hsp Hdst Hsrc Hcells CH Hn src dst c_rmc p_flag g_flag base.
    intros M beg raX s0 s1 HM HG Hlo Hhi R0 H0 R1 H1' RZ HR.
    clear Rzs Rzd Rs0s Rs1s Rs0d Rs1d Hs0s Hs1s Hs0d Hs1d.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range beg) as Hb.
    destruct CH as [C1 C2 C3 C4 C5 C6 C7 C8 CC Clo Chi]. cells_split.
    assert (SH : forall x, (0 <= x < 0x800000000000)%Z -> (0x7fff8000 <= Sh x < 0x10007fff8000)%Z).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos x 8). pose proof (Z.div_lt_upper_bound x 8 0x100000000000 ltac:(lia) ltac:(lia)). lia. }
    pose proof (SH (U beg) ltac:(lia)) as S0.
    pose proof (SH (U beg + n - 1)%Z ltac:(lia)) as S1.
    assert (UP : (U beg <= up8 (U beg) <= U beg + 7)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); pose proof (Z.div_mod (U beg + 7) 8); pose proof (Z.mod_pos_bound (U beg + 7) 8); lia).
    assert (DN : (U beg + n - 7 <= down8 (U beg + n) <= U beg + n)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (U beg + n) 8); pose proof (Z.mod_pos_bound (U beg + n) 8); lia).
    pose proof (SH (up8 (U beg)) ltac:(lia)) as S2. pose proof (SH (down8 (U beg + n)) ltac:(lia)) as S3.
    assert (Un : U (Z_to_bv 64 n) = n) by (apply u_Z2bv; lia).
    split.
    - split; [rdo HM C1 | rdo HM C2 | rdo HM C3 | rdo HM C4 | rdo HM C5 | rdo HM C6 | rdo HM C7 | rdo HM C8 | exact CC | lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat constructor; rewrite ?at_u; lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rdo HM R0.
    - exact H0.
    - rewrite Un. rdo HM R1.
    - rewrite Un. exact H1'.
    - rewrite Un. intros a Ha. pose proof (u64_range a). pose proof (RZ a Ha) as Ra.
      rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ra |- *. rdo HM Ra.
    - rewrite at_u by lia. lia.
    - rewrite at_at. replace (-2160 + -80)%Z with (-2240)%Z by lia. eapply store_ok_mono; [exact HG|].
      eapply (store_ok_sub segs mem (at_ sp (-2240)) _ 2240); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - exact HR.
  Qed.















  End WithRegs.
End ICPY.



End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
