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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Definition rip_words : list (option (bv 32)) :=
  [
   Some W_6ff90; Some W_6ff94; Some W_6ff98; Some W_6ff9c; Some W_6ffa0; Some W_6ffa4; Some W_6ffa8; Some
   W_6ffac; Some W_6ffb0; Some W_6ffb4; Some W_6ffb8; None; None; Some W_6ffc4; Some W_6ffc8; Some W_6ffcc; Some
   W_6ffd0; Some W_6ffd4; Some W_6ffd8; None; None; None; None; Some W_6ffec; Some W_6fff0; Some W_6fff4; Some
   W_6fff8; Some W_6fffc; None; None; Some W_70008; Some W_7000c; Some W_70010; Some W_70014; Some W_70018; Some
   W_7001c; Some W_70020; None; None; None; None; Some W_70034; Some W_70038; Some W_7003c; Some W_70040; Some
   W_70044; None; None; Some W_70050; Some W_70054; Some W_70058; Some W_7005c; Some W_70060; Some W_70064; Some
   W_70068; Some W_7006c; Some W_70070; Some W_70074; Some W_70078; Some W_7007c; Some W_70080; Some W_70084;
   Some W_70088; Some W_7008c; Some W_70090; Some W_70094; Some W_70098; Some W_7009c; Some W_700a0; Some
   W_700a4; Some W_700a8; Some W_700ac; Some W_700b0; Some W_700b4; Some W_700b8; Some W_700bc; Some W_700c0;
   Some W_700c4; Some W_700c8; Some W_700cc; Some W_700d0; Some W_700d4; Some W_700d8; Some W_700dc; Some
   W_700e0; Some W_700e4; Some W_700e8; Some W_700ec; Some W_700f0; Some W_700f4; Some W_700f8; Some W_700fc;
   Some W_70100; Some W_70104; Some W_70108; Some W_7010c; Some W_70110; Some W_70114; Some W_70118; Some
   W_7011c; Some W_70120; Some W_70124; Some W_70128; Some W_7012c; Some W_70130
  ]%list.


Definition rip_clob : list reg := [5; 10; 11; 12; 13; 14; 15; 16; 17].
Definition rip_clobx : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 5; 10; 11; 12; 13; 14; 15; 16; 17].

(* [comment removed for export] *)
Definition Sh (a : Z) : Z := (a / 8 + 0x7fff8000)%Z.
Definition up8 (a : Z) : Z := ((a + 7) / 8 * 8)%Z.
Definition down8 (a : Z) : Z := (a / 8 * 8)%Z.

Record rip_tab : Type := RIPT { rt_base : word; rt_m2s : m2s_tab }.

Record rip_tab_ok (segs : list Segment) (t : rip_tab) : Prop := RIPTOK {
  rto_code : code_ato segs (rt_base t) 0 rip_words;
  rto_m2s : m2s_tab_ok segs (rt_m2s t);
  rto_m2s_base : mt_base (rt_m2s t) = at_ (rt_base t) (-1164);
  rto_misz : code_at segs (at_ (rt_base t) 66768) 0 memisz_words;
  rto_g44 : gload2 segs (rt_base t) 44 10 21 (mt_g_shoff (rt_m2s t));
  rto_g76 : gload segs (rt_base t) 76 13 (mt_g_midbeg (rt_m2s t));
  rto_g84 : gload segs (rt_base t) 84 14 (mt_g_midend (rt_m2s t));
  rto_g112 : gload segs (rt_base t) 112 14 (mt_g_hiend (rt_m2s t));
  rto_g148 : gload segs (rt_base t) 148 12 (mt_g_midbeg (rt_m2s t));
  rto_g156 : gload segs (rt_base t) 156 13 (mt_g_midend (rt_m2s t));
  rto_g184 : gload segs (rt_base t) 184 13 (mt_g_hiend (rt_m2s t));
  rto_base : (bv_unsigned (rt_base t) mod 2 = 0)%Z /\ (2000 <= bv_unsigned (rt_base t))%Z /\ (bv_unsigned (rt_base t) + 90000 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Record ripH (segs : list Segment) (t : rip_tab) (mem : word -> option byte)
       (beg size ra sp : word) (s0b s1b : byte) (midend : word) : Prop := RIPH {
  rh_cellsH : m2sH segs (rt_m2s t) mem beg midend;    (* [comment removed for export] *)
  rh_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 80)%Z (m2s_cells (rt_m2s t));
  rh_size : (8 <= bv_unsigned size)%Z;     (* [comment removed for export] *)
  rh_end : ((0x10007fff8000 <= bv_unsigned beg /\ bv_unsigned beg + bv_unsigned size + 1 <= 0x800000000000)
            \/ bv_unsigned beg + bv_unsigned size <= 0x7fff7fff)%Z;   (* [comment removed for export] *)
  rh_sizemax : (bv_unsigned size <= 2 ^ 43)%Z;
  rh_s0 : rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned beg))) 1 = Some [s0b];
  rh_s0ok : (bv_unsigned s0b = 0 \/ bv_unsigned beg mod 8 < bv_unsigned s0b < 128)%Z;
  rh_s1 : rdn segs mem (Z_to_bv 64 (Sh (bv_unsigned beg + bv_unsigned size - 1))) 1 = Some [s1b];
  rh_s1ok : (bv_unsigned s1b = 0 \/ (bv_unsigned beg + bv_unsigned size - 1) mod 8 < bv_unsigned s1b < 128)%Z;
  rh_zero : forall a : word,
      (Sh (up8 (bv_unsigned beg)) <= bv_unsigned a < Sh (down8 (bv_unsigned beg + bv_unsigned size)))%Z ->
      rdn segs mem a 1 = Some [Z_to_bv 8 0];
  rh_sp : (0x10007fff8000 + 80 <= bv_unsigned sp)%Z /\ (bv_unsigned sp < 2 ^ 64)%Z;
  rh_stk : store_ok segs mem (at_ sp (-80)) 80 = true;
  rh_ret : ret_ok ra }.

(* [comment removed for export] *)
Definition rip_mem (t : rip_tab) (mem : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 beg size : word) : word -> option byte :=
  let M1 := ps_frame mem sp ra s0 s1 s2 s3 s4 s5 in
  if (Sh (up8 (bv_unsigned beg)) <? Sh (down8 (bv_unsigned beg + bv_unsigned size)))%Z
  then wbytes M1 (at_ sp (-72)) (word_to_le_bytes 8 (at_ (rt_base t) 372))
  else M1.

Section RIP.
  Variable segs : list Segment.
  Variable base : word.
  Variable tm : m2s_tab.
  Hypothesis HCODE : code_ato segs base 0 rip_words.
  Hypothesis TMOK : m2s_tab_ok segs tm.
  Hypothesis TMB : mt_base tm = at_ base (-1164).
  Hypothesis MISZ : code_at segs (at_ base 66768) 0 memisz_words.
  Hypothesis G44 : gload2 segs base 44 10 21 (mt_g_shoff tm).
  Hypothesis G76 : gload segs base 76 13 (mt_g_midbeg tm).
  Hypothesis G84 : gload segs base 84 14 (mt_g_midend tm).
  Hypothesis G112 : gload segs base 112 14 (mt_g_hiend tm).
  Hypothesis G148 : gload segs base 148 12 (mt_g_midbeg tm).
  Hypothesis G156 : gload segs base 156 13 (mt_g_midend tm).
  Hypothesis G184 : gload segs base 184 13 (mt_g_hiend tm).
  Hypothesis Hbase : (bv_unsigned base mod 2 = 0)%Z /\ (2000 <= bv_unsigned base)%Z /\ (bv_unsigned base + 90000 < 2 ^ 64)%Z.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_6ff90.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_6ff94.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_6ff98.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_6ff9c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_6ffa0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_6ffa4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_6ffa8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_6ffac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_6ffb0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_6ffb4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_6ffb8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_6ffc4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_6ffc8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_6ffcc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_6ffd0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_6ffd4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_6ffd8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo92 : fetch_word segs (at_ base 92) = Some W_6ffec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 23 _ HCODE eq_refl). Qed.
  Lemma Fo96 : fetch_word segs (at_ base 96) = Some W_6fff0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 24 _ HCODE eq_refl). Qed.
  Lemma Fo100 : fetch_word segs (at_ base 100) = Some W_6fff4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 25 _ HCODE eq_refl). Qed.
  Lemma Fo104 : fetch_word segs (at_ base 104) = Some W_6fff8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 26 _ HCODE eq_refl). Qed.
  Lemma Fo108 : fetch_word segs (at_ base 108) = Some W_6fffc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 27 _ HCODE eq_refl). Qed.
  Lemma Fo120 : fetch_word segs (at_ base 120) = Some W_70008.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 30 _ HCODE eq_refl). Qed.
  Lemma Fo124 : fetch_word segs (at_ base 124) = Some W_7000c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 31 _ HCODE eq_refl). Qed.
  Lemma Fo128 : fetch_word segs (at_ base 128) = Some W_70010.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 32 _ HCODE eq_refl). Qed.
  Lemma Fo132 : fetch_word segs (at_ base 132) = Some W_70014.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 33 _ HCODE eq_refl). Qed.
  Lemma Fo136 : fetch_word segs (at_ base 136) = Some W_70018.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 34 _ HCODE eq_refl). Qed.
  Lemma Fo140 : fetch_word segs (at_ base 140) = Some W_7001c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 35 _ HCODE eq_refl). Qed.
  Lemma Fo144 : fetch_word segs (at_ base 144) = Some W_70020.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 36 _ HCODE eq_refl). Qed.
  Lemma Fo164 : fetch_word segs (at_ base 164) = Some W_70034.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 41 _ HCODE eq_refl). Qed.
  Lemma Fo168 : fetch_word segs (at_ base 168) = Some W_70038.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 42 _ HCODE eq_refl). Qed.
  Lemma Fo172 : fetch_word segs (at_ base 172) = Some W_7003c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo176 : fetch_word segs (at_ base 176) = Some W_70040.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo180 : fetch_word segs (at_ base 180) = Some W_70044.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 45 _ HCODE eq_refl). Qed.
  Lemma Fo192 : fetch_word segs (at_ base 192) = Some W_70050.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 48 _ HCODE eq_refl). Qed.
  Lemma Fo196 : fetch_word segs (at_ base 196) = Some W_70054.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 49 _ HCODE eq_refl). Qed.
  Lemma Fo200 : fetch_word segs (at_ base 200) = Some W_70058.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 50 _ HCODE eq_refl). Qed.
  Lemma Fo204 : fetch_word segs (at_ base 204) = Some W_7005c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 51 _ HCODE eq_refl). Qed.
  Lemma Fo208 : fetch_word segs (at_ base 208) = Some W_70060.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 52 _ HCODE eq_refl). Qed.
  Lemma Fo212 : fetch_word segs (at_ base 212) = Some W_70064.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 53 _ HCODE eq_refl). Qed.
  Lemma Fo216 : fetch_word segs (at_ base 216) = Some W_70068.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 54 _ HCODE eq_refl). Qed.
  Lemma Fo220 : fetch_word segs (at_ base 220) = Some W_7006c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 55 _ HCODE eq_refl). Qed.
  Lemma Fo224 : fetch_word segs (at_ base 224) = Some W_70070.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 56 _ HCODE eq_refl). Qed.
  Lemma Fo228 : fetch_word segs (at_ base 228) = Some W_70074.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 57 _ HCODE eq_refl). Qed.
  Lemma Fo232 : fetch_word segs (at_ base 232) = Some W_70078.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 58 _ HCODE eq_refl). Qed.
  Lemma Fo236 : fetch_word segs (at_ base 236) = Some W_7007c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 59 _ HCODE eq_refl). Qed.
  Lemma Fo240 : fetch_word segs (at_ base 240) = Some W_70080.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 60 _ HCODE eq_refl). Qed.
  Lemma Fo244 : fetch_word segs (at_ base 244) = Some W_70084.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 61 _ HCODE eq_refl). Qed.
  Lemma Fo248 : fetch_word segs (at_ base 248) = Some W_70088.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 62 _ HCODE eq_refl). Qed.
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_7008c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_70090.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_70094.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo264 : fetch_word segs (at_ base 264) = Some W_70098.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 66 _ HCODE eq_refl). Qed.
  Lemma Fo268 : fetch_word segs (at_ base 268) = Some W_7009c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 67 _ HCODE eq_refl). Qed.
  Lemma Fo272 : fetch_word segs (at_ base 272) = Some W_700a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 68 _ HCODE eq_refl). Qed.
  Lemma Fo276 : fetch_word segs (at_ base 276) = Some W_700a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 69 _ HCODE eq_refl). Qed.
  Lemma Fo280 : fetch_word segs (at_ base 280) = Some W_700a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 70 _ HCODE eq_refl). Qed.
  Lemma Fo284 : fetch_word segs (at_ base 284) = Some W_700ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 71 _ HCODE eq_refl). Qed.
  Lemma Fo288 : fetch_word segs (at_ base 288) = Some W_700b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 72 _ HCODE eq_refl). Qed.
  Lemma Fo292 : fetch_word segs (at_ base 292) = Some W_700b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 73 _ HCODE eq_refl). Qed.
  Lemma Fo296 : fetch_word segs (at_ base 296) = Some W_700b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 74 _ HCODE eq_refl). Qed.
  Lemma Fo300 : fetch_word segs (at_ base 300) = Some W_700bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 75 _ HCODE eq_refl). Qed.
  Lemma Fo304 : fetch_word segs (at_ base 304) = Some W_700c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 76 _ HCODE eq_refl). Qed.
  Lemma Fo308 : fetch_word segs (at_ base 308) = Some W_700c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 77 _ HCODE eq_refl). Qed.









  Lemma Fo348 : fetch_word segs (at_ base 348) = Some W_700ec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 87 _ HCODE eq_refl). Qed.

  Lemma Fo356 : fetch_word segs (at_ base 356) = Some W_700f4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 89 _ HCODE eq_refl). Qed.
  Lemma Fo360 : fetch_word segs (at_ base 360) = Some W_700f8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 90 _ HCODE eq_refl). Qed.
  Lemma Fo364 : fetch_word segs (at_ base 364) = Some W_700fc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 91 _ HCODE eq_refl). Qed.
  Lemma Fo368 : fetch_word segs (at_ base 368) = Some W_70100.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 92 _ HCODE eq_refl). Qed.
  Lemma Fo372 : fetch_word segs (at_ base 372) = Some W_70104.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 93 _ HCODE eq_refl). Qed.
  Lemma Fo376 : fetch_word segs (at_ base 376) = Some W_70108.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 94 _ HCODE eq_refl). Qed.
  Lemma Fo380 : fetch_word segs (at_ base 380) = Some W_7010c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 95 _ HCODE eq_refl). Qed.
  Lemma Fo384 : fetch_word segs (at_ base 384) = Some W_70110.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 96 _ HCODE eq_refl). Qed.
  Lemma Fo388 : fetch_word segs (at_ base 388) = Some W_70114.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 97 _ HCODE eq_refl). Qed.
  Lemma Fo392 : fetch_word segs (at_ base 392) = Some W_70118.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 98 _ HCODE eq_refl). Qed.
  Lemma Fo396 : fetch_word segs (at_ base 396) = Some W_7011c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 99 _ HCODE eq_refl). Qed.
  Lemma Fo400 : fetch_word segs (at_ base 400) = Some W_70120.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 100 _ HCODE eq_refl). Qed.
  Lemma Fo404 : fetch_word segs (at_ base 404) = Some W_70124.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 101 _ HCODE eq_refl). Qed.
  Lemma Fo408 : fetch_word segs (at_ base 408) = Some W_70128.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 102 _ HCODE eq_refl). Qed.
  Lemma Fo412 : fetch_word segs (at_ base 412) = Some W_7012c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 103 _ HCODE eq_refl). Qed.
  Lemma Fo416 : fetch_word segs (at_ base 416) = Some W_70130.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 rip_words 104 _ HCODE eq_refl). Qed.


  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables beg size ra sp : word.
  Variables s0b s1b : byte.
  Variable midend : word.

  #[local] Abbreviation U := bv_unsigned.
  #[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).
  #[local] Abbreviation endZ := (bv_unsigned beg + bv_unsigned size)%Z.

  Hypothesis CH : m2sH segs tm mem beg midend.
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 80)%Z (m2s_cells tm).
  Hypothesis Hsize : (8 <= U size)%Z.
  Hypothesis Hend : ((0x10007fff8000 <= U beg /\ endZ + 1 <= 0x800000000000) \/ endZ <= 0x7fff7fff)%Z.
  Hypothesis HsizeMax : (U size <= 2 ^ 43)%Z.   (* [comment removed for export] *)
  Hypothesis Rs0 : rdn segs mem (Z_to_bv 64 (Sh (U beg))) 1 = Some [s0b].
  Hypothesis Hs0 : (U s0b = 0 \/ U beg mod 8 < U s0b < 128)%Z.
  Hypothesis Rs1 : rdn segs mem (Z_to_bv 64 (Sh (endZ - 1))) 1 = Some [s1b].
  Hypothesis Hs1 : (U s1b = 0 \/ (endZ - 1) mod 8 < U s1b < 128)%Z.
  Hypothesis Rzero : forall a : word,
      (Sh (up8 (U beg)) <= U a < Sh (down8 endZ))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0].
  Hypothesis Hsp : (0x10007fff8000 + 80 <= U sp)%Z /\ (U sp < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-80)) 80 = true.
  Hypothesis Hret : ret_ok ra.

  #[local] Abbreviation CL := (fun r => In r rip_clob).
  #[local] Abbreviation CLX := (fun r => In r rip_clobx).

  (* [comment removed for export] *)
  Lemma rip_arith :
    ((0x10007fff8000 <= U beg /\ endZ <= 0x7fffffffffff) \/ endZ <= 0x7fff7fff)%Z /\ (endZ <= 0x7fffffffffff)%Z /\
    (U beg <= up8 (U beg) <= U beg + 7)%Z /\ (up8 (U beg) mod 8 = 0)%Z /\
    (endZ - 7 <= down8 endZ <= endZ /\ (0x10007fff8000 <= U beg -> 0x10007fff8000 <= down8 endZ))%Z /\ (down8 endZ mod 8 = 0)%Z /\
    (forall x, 0 <= x <= 0x800000000000 -> 0x7fff8000 <= Sh x <= 0x10007fff8000)%Z /\
    (Sh (up8 (U beg)) = up8 (U beg) / 8 + 0x7fff8000)%Z /\ (Sh (down8 endZ) = down8 endZ / 8 + 0x7fff8000)%Z /\
    (Sh (down8 endZ) - Sh (up8 (U beg)) <= 2 ^ 40)%Z.
  Proof using HsizeMax Hend Hsize CH midend mem tm base segs.
    destruct CH as [_ _ _ _ _ _ _ _ _ Hlo Hhi]. pose proof (u64_range beg). pose proof (u64_range size).
    pose proof (Z.div_mod (U beg + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (U beg + 7) 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod endZ 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound endZ 8 ltac:(lia)) as M2.
    assert (E1 : (up8 (U beg) mod 8 = 0)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); apply Z.mod_mul; lia).
    assert (E2 : (down8 endZ mod 8 = 0)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); apply Z.mod_mul; lia).
    assert (S1 : forall x, (0 <= x <= 0x800000000000)%Z -> (0x7fff8000 <= Sh x <= 0x10007fff8000)%Z).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos x 8).
      pose proof (Z.div_le_mono x 0x800000000000 8 ltac:(lia) ltac:(lia)).
      change (0x800000000000 / 8)%Z with 0x100000000000%Z in *. lia. }
    assert (S2 : (Sh (up8 (U beg)) = up8 (U beg) / 8 + 0x7fff8000)%Z) by reflexivity.
    assert (S3 : (Sh (down8 endZ) = down8 endZ / 8 + 0x7fff8000)%Z) by reflexivity.
    assert (Q1 : (up8 (U beg) / 8 = (U beg + 7) / 8)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); rewrite Z.div_mul; lia).
    assert (Q2 : (down8 endZ / 8 = endZ / 8)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); rewrite Z.div_mul; lia).
    pose proof (Z.div_le_mono (U beg + 7) (endZ + 7) 8 ltac:(lia) ltac:(lia)) as Q3.
    assert (Q4 : (0x10007fff8000 <= endZ -> 0x2000ffff000 <= endZ / 8)%Z).
    { intros HE. pose proof (Z.div_le_mono 0x10007fff8000 endZ 8 ltac:(lia) HE) as Q4. change (0x10007fff8000 / 8)%Z with 0x2000ffff000%Z in Q4. exact Q4. }
    clear - Hsize Hend HsizeMax Hlo Hhi H H0 D1 M1 D2 M2 E1 E2 S1 S2 S3 Q1 Q2 Q3 Q4.
    unfold up8, down8 in *.
    (* [comment removed for export] *)
    repeat split;
      [ lia | lia
      | first [ solve [clear - D1 M1; lia] | lia ]
      | first [ solve [clear - D1 M1; lia] | lia ]
      | first [ exact E1 | lia ]
      | first [ solve [clear - D2 M2; lia] | lia ]
      | first [ solve [clear - D2 M2; lia] | lia ]
      | first [ solve [clear - D2 M2 Hsize; lia] | lia ]
      | first [ exact E2 | lia ]
      | match goal with Hy : (0 <= ?y <= _)%Z |- _ => let HS := fresh "HS" in pose proof (S1 y Hy) as HS; first [ solve [clear - HS; lia] | lia ] end
      | match goal with Hy : (0 <= ?y <= _)%Z |- _ => let HS := fresh "HS" in pose proof (S1 y Hy) as HS; first [ solve [clear - HS; lia] | lia ] end
      | first [ solve [clear - S2 S3 Q1 Q2 D1 M1 D2 M2 HsizeMax; lia] | lia ] ].
  Qed.

  Section WithRegs.
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = beg.
  Hypothesis H11 : getr regs 11 = size.

  Definition RM1 : word -> option byte :=
    ps_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21).

  Lemma rdRM1 : forall c n bs, (0 <= c)%Z -> (c + Z.of_nat n <= U sp - 64)%Z ->
    rdn segs mem (Z_to_bv 64 c) n = Some bs -> rdn segs RM1 (Z_to_bv 64 c) n = Some bs.
  Proof using Hsp Hsize size beg Hbase base.
    intros c n bs Hc0 Hc Hr. (lazymatch goal with |- ?G => let G' := eval unfold RM1, ps_frame in G in change_no_check G' end). pose proof (u64_range sp).
    rewrite !rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); unorm; try lia.
    exact Hr.
  Qed.

  Lemma rdRM1w : forall (a : word) n bs, (U a + Z.of_nat n <= U sp - 64)%Z ->
    rdn segs mem a n = Some bs -> rdn segs RM1 a n = Some bs.
  Proof using Hsp Hsize size beg Hbase base.
    intros a n bs Ha Hr. pose proof (u64_range a). rewrite <- (Z_to_bv_bv_unsigned 64 a) in Hr |- *.
    apply rdRM1; try lia. exact Hr.
  Qed.

  Lemma RM1_ok : forall (a : word) n, store_ok segs mem a n = true -> store_ok segs RM1 a n = true.
  Proof using. intros a n H. (lazymatch goal with |- ?G => let G' := eval unfold RM1, ps_frame in G in change_no_check G' end). repeat (eapply store_ok_mono; [apply wbytes_grows|]). exact H. Qed.

  (* [comment removed for export] *)
  Lemma m2sH_RM1 : forall p : word, (0x10007fff8000 <= U p \/ U p <= 0x7fff7fff)%Z -> (U p <= 0x7fffffffffff)%Z -> m2sH segs tm RM1 p midend.
  Proof using Hsp Hsize Hcells CH size beg Hbase base.
    intros p Hlo Hhi. destruct CH as [R1 R2 R3 R4 R5 R6 R7 R8 HC _ _].
    pose proof Hcells as HC'. unfold m2s_cells in HC'.
    repeat match type of HC' with Forall _ (_ :: _) => apply Forall_cons_iff in HC'; destruct HC' as [? HC'] end.
    split; try assumption; apply rdRM1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia; assumption.
  Qed.

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
          eapply (store_ok_sub segs mem (at_ sp (-80)) _ 80);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac cld F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?v_addi_0;
          first [ apply rdRM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr]
                | (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; apply rdRM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr] ]
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac gl G Hr :=
    eapply msteps_trans; [ eapply G; apply rdRM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr] | ]; zlit_at.
  Ltac fld F D vv :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold RM1, ps_frame in G in change_no_check G' end); rd8_chain
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rblkA :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 44) RM1 rom)
      /\ getr r 1 = ra /\ getr r 2 = at_ sp (-64) /\ getr r 8 = beg /\ getr r 9 = size
      /\ regs_agree CLX regs r.
  Proof using H11 H10 H2 H1 Hstk Hsp Hsize HCODE.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range size) as Hsz.
    wd_eexists. split.
    - an Fo0 D_6ff90.                                   (* [comment removed for export] *)
      fsd Fo4 D_6ff94 (at_ sp (-8)).                     (* [comment removed for export] *)
      fsd Fo8 D_6ff98 (at_ sp (-16)).                    (* [comment removed for export] *)
      fsd Fo12 D_6ff9c (at_ sp (-24)).                   (* [comment removed for export] *)
      fsd Fo16 D_6ffa0 (at_ sp (-32)).                   (* [comment removed for export] *)
      fsd Fo20 D_6ffa4 (at_ sp (-40)).                   (* [comment removed for export] *)
      fsd Fo24 D_6ffa8 (at_ sp (-48)).                   (* [comment removed for export] *)
      fsd Fo28 D_6ffac (at_ sp (-56)).                   (* [comment removed for export] *)
      change (wbytes _ _ _) with RM1.
      ab_ft Fo32 D_6ffb0 ltac:(condz).                   (* [comment removed for export] *)
      an Fo36 D_6ffb4.                                     (* [comment removed for export] *)
      an Fo40 D_6ffb8.                                     (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end); solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rblkB : forall r0,
    getr r0 1 = ra -> getr r0 2 = at_ sp (-64) -> getr r0 8 = beg -> getr r0 9 = size ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 44) RM1 rom) (mkst r (at_ base (-1164)) RM1 rom)
      /\ getr r 1 = at_ base 232 /\ getr r 2 = at_ sp (-64) /\ getr r 8 = beg /\ getr r 9 = size
      /\ getr r 10 = Z_to_bv 64 (up8 (U beg)) /\ getr r 18 = Z_to_bv 64 endZ /\ getr r 20 = Z_to_bv 64 (down8 endZ)
      /\ getr r 21 = Z_to_bv 64 (mt_p_shoff tm)
      /\ regs_agree CLX regs r.
  Proof using Hsp HsizeMax Hend Hsize Hcells CH midend Hbase G184 G156 G148 G112 G84 G76 G44 HCODE.
    intros r0 R1 R2 R8 R9 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range beg) as Hb. pose proof (u64_range size) as Hsz.
    destruct rip_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    destruct CH as [R1' R2' R3' R4' R5' R6' R7' R8' _ _ _].
    cells_split. destruct G44 as [x44 GX44].
    destruct A1 as [[HI _] | LO].
    2:{ (* [comment removed for export] *)
    wd_eexists. split.
    - eapply msteps_trans; [ eapply GX44; apply rdRM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact R1'] | ]; zlit_at.
      cld Fo52 D_6ffc4 (Z_to_bv 64 0x7fff8000) R2'.       (* [comment removed for export] *)
      an Fo56 D_6ffc8. an Fo60 D_6ffcc. an Fo64 D_6ffd0. an Fo68 D_6ffd4.   (* [comment removed for export] *)
      ab_tk Fo72 D_6ffd8 ltac:(condz).                   (* [comment removed for export] *)
      av Fo140 D_7001c (Z_to_bv 64 endZ) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); f_equal; lia).   (* [comment removed for export] *)
      ab_tk Fo144 D_70020 ltac:(condz).                  (* [comment removed for export] *)
      ab_ft Fo212 D_70064 ltac:(condz).                  (* [comment removed for export] *)
      av Fo216 D_70068 (Z_to_bv 64 (U beg + 7)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); reflexivity).            (* [comment removed for export] *)
      av Fo220 D_7006c (Z_to_bv 64 (up8 (U beg)))
         ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 4088) with (2 ^ 64 - 2 ^ 3)%Z; unorm; rewrite land_m8 by lia;
               (lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); f_equal; pose proof (Z.div_mod (U beg + 7) 8 ltac:(lia)); lia).   (* [comment removed for export] *)
      av Fo224 D_70070 (Z_to_bv 64 (down8 endZ))
         ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 4088) with (2 ^ 64 - 2 ^ 3)%Z; unorm; rewrite land_m8 by lia;
               (lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); f_equal; pose proof (Z.div_mod endZ 8 ltac:(lia)); lia).          (* [comment removed for export] *)
      an Fo228 D_70074.                                    (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end). ra_chain. }
    wd_eexists. split.
    - eapply msteps_trans; [ eapply GX44; apply rdRM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact R1'] | ]; zlit_at.
      cld Fo52 D_6ffc4 (Z_to_bv 64 0x7fff8000) R2'.       (* [comment removed for export] *)
      an Fo56 D_6ffc8. an Fo60 D_6ffcc. an Fo64 D_6ffd0. an Fo68 D_6ffd4.   (* [comment removed for export] *)
      ab_ft Fo72 D_6ffd8 ltac:(condz).                   (* [comment removed for export] *)
      gl G76 R3'. gl G84 R5'.
      cld Fo92 D_6ffec (Z_to_bv 64 0) R4'.                (* [comment removed for export] *)
      cld Fo96 D_6fff0 midend R6'.                         (* [comment removed for export] *)
      an Fo100 D_6fff4.                                    (* [comment removed for export] *)
      ab_tk Fo104 D_6fff8 ltac:(condz).                  (* [comment removed for export] *)
      gl G112 R7'.
      cld Fo120 D_70008 (Z_to_bv 64 0x7fffffffffff) R8'.  (* [comment removed for export] *)
      an Fo124 D_7000c. an Fo128 D_70010.
      ab_ft Fo132 D_70014 ltac:(condz).                  (* [comment removed for export] *)
      ab_ft Fo136 D_70018 ltac:(condz).                  (* [comment removed for export] *)
      av Fo140 D_7001c (Z_to_bv 64 endZ) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); f_equal; lia).   (* [comment removed for export] *)
      ab_ft Fo144 D_70020 ltac:(condz).                  (* [comment removed for export] *)
      gl G148 R3'. gl G156 R5'.
      cld Fo164 D_70034 (Z_to_bv 64 0) R4'.               (* [comment removed for export] *)
      cld Fo168 D_70038 midend R6'.                        (* [comment removed for export] *)
      an Fo172 D_7003c.                                    (* [comment removed for export] *)
      ab_tk Fo176 D_70040 ltac:(condz).                  (* [comment removed for export] *)
      gl G184 R7'.
      cld Fo192 D_70050 (Z_to_bv 64 0x7fffffffffff) R8'.  (* [comment removed for export] *)
      an Fo196 D_70054. an Fo200 D_70058.
      ab_ft Fo204 D_7005c ltac:(condz).                  (* [comment removed for export] *)
      ab_ft Fo208 D_70060 ltac:(condz).                  (* [comment removed for export] *)
      ab_ft Fo212 D_70064 ltac:(condz).                  (* [comment removed for export] *)
      av Fo216 D_70068 (Z_to_bv 64 (U beg + 7)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); reflexivity).            (* [comment removed for export] *)
      av Fo220 D_7006c (Z_to_bv 64 (up8 (U beg)))
         ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 4088) with (2 ^ 64 - 2 ^ 3)%Z; unorm; rewrite land_m8 by lia;
               (lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); f_equal; pose proof (Z.div_mod (U beg + 7) 8 ltac:(lia)); lia).   (* [comment removed for export] *)
      av Fo224 D_70070 (Z_to_bv 64 (down8 endZ))
         ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 4088) with (2 ^ 64 - 2 ^ 3)%Z; unorm; rewrite land_m8 by lia;
               (lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); f_equal; pose proof (Z.div_mod endZ 8 ltac:(lia)); lia).          (* [comment removed for export] *)
      an Fo228 D_70074.                                    (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end). ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma rblkC : forall r0 (x10 : word),
    getr r0 2 = at_ sp (-64) -> getr r0 10 = x10 -> getr r0 20 = Z_to_bv 64 (down8 endZ) ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 232) RM1 rom) (mkst r (at_ base (-1164)) RM1 rom)
      /\ getr r 1 = at_ base 244 /\ getr r 2 = at_ sp (-64) /\ getr r 19 = x10 /\ getr r 10 = Z_to_bv 64 (down8 endZ)
      /\ (forall i : reg, In i [8; 9; 18; 20; 21] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using HCODE.
    intros r0 x10 R2 R10 R20 AG0.
    wd_eexists. split.
    - an Fo232 D_70078.                                  (* [comment removed for export] *)
      an Fo236 D_7007c.                                  (* [comment removed for export] *)
      an Fo240 D_70080.                                  (* [comment removed for export] *)
      wd_refl.
    - post. 2: (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end); ra_chain.
      intros i Hi. cbn [In] in Hi.
      repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]). destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma rblkD : forall r0,
    getr r0 2 = at_ sp (-64) -> getr r0 8 = beg -> getr r0 18 = Z_to_bv 64 endZ -> getr r0 21 = Z_to_bv 64 (mt_p_shoff tm) ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 244) RM1 rom) (mkst r (at_ base 356) RM1 rom)
      /\ getr r 2 = at_ sp (-64)
      /\ (forall i : reg, In i [1; 8; 9; 10; 19; 20; 21] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using Hsp Hs1 Rs1 Hs0 Rs0 HsizeMax Hend Hsize Hcells CH midend s1b s0b Hbase HCODE.
    intros r0 R2 R8 R18 R21 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range beg) as Hb. pose proof (u64_range size) as Hsz.
    pose proof (u8_range s0b) as Hs0r. pose proof (u8_range s1b) as Hs1r.
    destruct rip_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    destruct CH as [R1' R2' R3' R4' R5' R6' R7' R8' _ _ _].
    pose proof (A7 (U beg) ltac:(lia)) as S0r. pose proof (A7 (endZ - 1)%Z ltac:(lia)) as S1r.
    cells_split.
    pose proof (Z.mod_pos_bound (U beg) 8 ltac:(lia)) as M0. pose proof (Z.mod_pos_bound (endZ - 1)%Z 8 ltac:(lia)) as M1.
    assert (Dv0 : (0 <= U beg / 8 <= 2 ^ 44)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (Dv1 : (0 <= (endZ - 1) / 8 <= 2 ^ 44)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).

    (* [comment removed for export] *)
    Ltac slb F D bb Hr :=
      chain_step; [reflexivity
        | eapply step_lb with (b := bb);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?v_addi_0; apply rdRM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr] ]
        | step_simpl]; vn.
    (* [comment removed for export] *)
    Ltac pre Rsh :=
      cld Fo244 D_70084 (Z_to_bv 64 0x7fff8000) Rsh;                                          (* [comment removed for export] *)
      av Fo248 D_70088 (Z_to_bv 64 (U beg / 8)) ltac:(apply v_srli_3);                         (* [comment removed for export] *)
      av Fo252 D_7008c (Z_to_bv 64 (Sh (U beg))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, Sh in G in change_no_check G' end); unorm; f_equal; lia); (* [comment removed for export] *)
      slb Fo256 D_70090 s0b Rs0.                                                                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    Ltac t1z := ab_tk Fo260 D_70094 ltac:(rewrite (v_lb_small s0b) by lia; condz).            (* [comment removed for export] *)
    Ltac t1nz :=
      ab_ft Fo260 D_70094 ltac:(condz);                                                        (* [comment removed for export] *)
      av Fo264 D_70098 (Z_to_bv 64 (U beg mod 8))
         ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 7) with 7%Z; unorm; rewrite land_7 by lia; reflexivity);  (* [comment removed for export] *)
      ab_ft Fo268 D_7009c ltac:(rewrite (v_lb_small s0b) by lia; condzs).                     (* [comment removed for export] *)
    (* [comment removed for export] *)
    Ltac mid :=
      av Fo272 D_700a0 (Z_to_bv 64 (endZ - 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia);      (* [comment removed for export] *)
      av Fo276 D_700a4 (Z_to_bv 64 ((endZ - 1) / 8)) ltac:(rewrite v_srli_3; unorm; reflexivity);  (* [comment removed for export] *)
      av Fo280 D_700a8 (Z_to_bv 64 (Sh (endZ - 1))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, Sh in G in change_no_check G' end); unorm; f_equal; lia);  (* [comment removed for export] *)
      slb Fo284 D_700ac s1b Rs1.                                                                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    Ltac t2z := ab_tk Fo288 D_700b0 ltac:(rewrite (v_lb_small s1b) by lia; condz).            (* [comment removed for export] *)
    Ltac t2nz :=
      ab_ft Fo288 D_700b0 ltac:(condz);                                                        (* [comment removed for export] *)
      av Fo292 D_700b4 (Z_to_bv 64 ((endZ - 1) mod 8))
         ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 7) with 7%Z; unorm; rewrite land_7 by lia; reflexivity);  (* [comment removed for export] *)
      ab_tk Fo296 D_700b8 ltac:(rewrite (v_lb_small s1b) by lia; condzs).                     (* [comment removed for export] *)
    Ltac fin :=
      post; [ intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi
            | (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end); ra_chain ].
    clear A1 A5 A7 A10 Hend HsizeMax Rzero Hcells.
    destruct Hs0 as [Z0|NZ0]; [|pose proof (u_v_lb_nz s0b ltac:(lia))];
    destruct Hs1 as [Z1|NZ1]; try pose proof (u_v_lb_nz s1b ltac:(lia)).
    - wd_eexists. split; [pre R2'; t1z; mid; t2z; wd_refl | fin].
    - wd_eexists. split; [pre R2'; t1z; mid; t2nz; wd_refl | fin].
    - wd_eexists. split; [pre R2'; t1nz; mid; t2z; wd_refl | fin].
    - wd_eexists. split; [pre R2'; t1nz; mid; t2nz; wd_refl | fin].
  Qed.

  (* [comment removed for export] *)
  Lemma rblkE0 : forall r0,
    getr r0 19 = Z_to_bv 64 (Sh (up8 (U beg))) -> getr r0 10 = Z_to_bv 64 (Sh (down8 endZ)) ->
    (Sh (down8 endZ) <= Sh (up8 (U beg)))%Z ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 356) RM1 rom) (mkst r (at_ base 376) RM1 rom)
      /\ (forall i : reg, getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using HsizeMax Hend Hsize CH midend Hbase HCODE tm.
    intros r0 R19 R10 Hle AG0. pose proof (u64_range beg). pose proof (u64_range size).
    destruct rip_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    pose proof (A7 (up8 (U beg)) ltac:(lia)). pose proof (A7 (down8 endZ) ltac:(lia)).
    wd_eexists. split.
    - ab_tk Fo356 D_700f4 ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - split; [intros i; reflexivity | exact AG0].
  Qed.

  (* [comment removed for export] *)
  Lemma rblkE1 : forall r0,
    getr r0 19 = Z_to_bv 64 (Sh (up8 (U beg))) -> getr r0 10 = Z_to_bv 64 (Sh (down8 endZ)) ->
    (Sh (up8 (U beg)) < Sh (down8 endZ))%Z ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 356) RM1 rom) (mkst r (at_ base 66768) RM1 rom)
      /\ getr r 1 = at_ base 372 /\ getr r 10 = Z_to_bv 64 (Sh (up8 (U beg)))
      /\ getr r 11 = Z_to_bv 64 (Sh (down8 endZ) - Sh (up8 (U beg)))
      /\ (forall i : reg, In i [2; 8; 9; 18; 19; 20; 21] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using HsizeMax Hend Hsize CH midend Hbase HCODE tm.
    intros r0 R19 R10 Hlt AG0. pose proof (u64_range beg). pose proof (u64_range size).
    destruct rip_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    pose proof (A7 (up8 (U beg)) ltac:(lia)). pose proof (A7 (down8 endZ) ltac:(lia)).
    wd_eexists. split.
    - ab_ft Fo356 D_700f4 ltac:(condz).              (* [comment removed for export] *)
      av Fo360 D_700f8 (Z_to_bv 64 (Sh (down8 endZ) - Sh (up8 (U beg)))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; reflexivity).  (* [comment removed for export] *)
      an Fo364 D_700fc.                                (* [comment removed for export] *)
      an Fo368 D_70100.                                (* [comment removed for export] *)
      wd_refl.
    - post. 2: (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end); ra_chain.
      intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma rblkF : forall (M : word -> option byte) r0 (pc0 : Z),
    (pc0 = 372 /\ getr r0 10 = Z_to_bv 64 1 \/ pc0 = 376)%Z ->
    getr r0 2 = at_ sp (-64) ->
    (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18);
                                           (-40, getr regs 19); (-48, getr regs 20); (-56, getr regs 21)]%Z ->
       rdn segs M (at_ sp k) 8 = Some (word_to_le_bytes 8 v)) ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base pc0) M rom) (mkst r ra M rom)
      /\ getr r 10 = Z_to_bv 64 0
      /\ regs_agree CL regs r.
  Proof using H2 H1 Hret HCODE.
    intros M r0 pc0 Hpc R2 RD AG0. pose proof (u64_range sp) as Hspr.
    Ltac fldM F D vv RD :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply RD; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); am_tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    Ltac tail RD :=
      an Fo376 D_70108;                                  (* [comment removed for export] *)
      an Fo380 D_7010c;                                  (* [comment removed for export] *)
      fldM Fo384 D_70110 ra RD;                          (* [comment removed for export] *)
      fldM Fo388 D_70114 (getr regs 8) RD;
      fldM Fo392 D_70118 (getr regs 9) RD;
      fldM Fo396 D_7011c (getr regs 18) RD;
      fldM Fo400 D_70120 (getr regs 19) RD;
      fldM Fo404 D_70124 (getr regs 20) RD;
      fldM Fo408 D_70128 (getr regs 21) RD;
      an Fo412 D_7012c;                                  (* [comment removed for export] *)
      aret Fo416 D_70130 ra;                             (* [comment removed for export] *)
      wd_refl.
    assert (FIN : forall r, regs_agree CLX regs r -> getr r 1 = ra -> getr r 2 = sp ->
              getr r 8 = getr regs 8 -> getr r 9 = getr regs 9 -> getr r 18 = getr regs 18 -> getr r 19 = getr regs 19 ->
              getr r 20 = getr regs 20 -> getr r 21 = getr regs 21 -> regs_agree CL regs r).
    { intros r AG E1 E2 E8 E9 E18 E19 E20 E21.
      apply (regs_agree_strengthen rip_clob rip_clobx regs r AG).
      intros i Hi Hn. cbn [rip_clobx In] in Hi.
      repeat (destruct Hi as [<-|Hi]; [first [rewrite <- H1 in E1; exact E1 | rewrite <- H2 in E2; exact E2 | assumption | exfalso; apply Hn; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto] |]).
      destruct Hi. }
    destruct Hpc as [[-> R10] | ->].
    - wd_eexists. split; [|split].
      + ab_ft Fo372 D_70104 ltac:(condz).              (* [comment removed for export] *)
        tail RD.
      + gres. reflexivity.
      + apply FIN; gres; rwH; rewrite ?at_addi, ?at_0; try reflexivity; try (f_equal; lia). (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end); ra_solve.
    - wd_eexists. split; [|split].
      + tail RD.
      + gres. reflexivity.
      + apply FIN; gres; rwH; rewrite ?at_addi, ?at_0; try reflexivity; try (f_equal; lia). (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end); ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma RM1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18);
               (-40, getr regs 19); (-48, getr regs 20); (-56, getr regs 21)]%Z ->
    rdn segs RM1 (at_ sp k) 8 = Some (word_to_le_bytes 8 v)
    /\ forall w : word, rdn segs (wbytes RM1 (at_ sp (-72)) (word_to_le_bytes 8 w)) (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp size beg base.
    intros k v Hin. pose proof (u64_range sp). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; split; [|intros w]; (lazymatch goal with |- ?G => let G' := eval unfold RM1, ps_frame in G in change_no_check G' end); rd8_chain|]).
    destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Definition RMF : word -> option byte :=
    if (Sh (up8 (U beg)) <? Sh (down8 endZ))%Z
    then wbytes RM1 (at_ sp (-72)) (word_to_le_bytes 8 (at_ base 372)) else RM1.

  Theorem rip_run :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra RMF rom)
      /\ getr r 10 = Z_to_bv 64 0
      /\ regs_agree CL regs r.
  Proof using H11 H10 H2 H1 Hret Hstk Hsp Rzero Hs1 Rs1 Hs0 Rs0 HsizeMax Hend Hsize Hcells CH midend s1b s0b Hbase G184 G156 G148 G112 G84 G76 G44 MISZ TMB TMOK HCODE tm.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range beg) as Hb. pose proof (u64_range size) as Hsz.
    destruct Hbase as (HB1 & HB2 & HB3).
    destruct rip_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    pose proof (A7 (up8 (U beg)) ltac:(lia)) as Sup. pose proof (A7 (down8 endZ) ltac:(lia)) as Sdn.
    assert (RA1 : ret_ok (at_ base 232)) by (apply ret_ok_at; [exact HB1 | reflexivity | lia]).
    assert (RA2 : ret_ok (at_ base 244)) by (apply ret_ok_at; [exact HB1 | reflexivity | lia]).
    assert (RA3 : ret_ok (at_ base 372)) by (apply ret_ok_at; [exact HB1 | reflexivity | lia]).
    destruct rblkA as (r1 & RUN1 & A1' & A2' & A8' & A9' & AG1).
    destruct (rblkB r1 A1' A2' A8' A9' AG1) as (r2 & RUN2 & B1 & B2 & B8 & B9 & B10 & B18 & B20 & B21 & AG2).
    (* [comment removed for export] *)
    destruct (m2s_run segs tm TMOK RM1 rom (Z_to_bv 64 (up8 (U beg))) midend (at_ base 232) r2
                (m2sH_RM1 (Z_to_bv 64 (up8 (U beg))) ltac:(wd_ulia) ltac:(wd_ulia)) B10 B1 RA1)
      as (r3 & RUN3 & C10 & AG3).
    rewrite TMB in RUN3.
    assert (C2 : getr r3 2 = at_ sp (-64)) by (rewrite (AG3 2%bv) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate); exact B2).
    assert (C20 : getr r3 20 = Z_to_bv 64 (down8 endZ)) by (rewrite (AG3 20%bv) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate); exact B20).
    assert (AG3x : regs_agree CLX regs r3).
    { intros i Hi. rewrite (AG3 i). apply AG2, Hi. intros Hm. apply Hi. unfold m2s_clob in Hm. cbn [In] in Hm. (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end). repeat (destruct Hm as [<-|Hm]; [(lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat first [left; reflexivity | right] |]). destruct Hm. }
    destruct (rblkC r3 _ C2 C10 C20 AG3x) as (r4 & RUN4 & D1 & D2 & D19 & D10 & DK & AG4).
    (* [comment removed for export] *)
    destruct (m2s_run segs tm TMOK RM1 rom (Z_to_bv 64 (down8 endZ)) midend (at_ base 244) r4
                (m2sH_RM1 (Z_to_bv 64 (down8 endZ)) ltac:(wd_ulia) ltac:(wd_ulia)) D10 D1 RA2)
      as (r5 & RUN5 & E10 & AG5).
    rewrite TMB in RUN5.
    assert (AGR5 : forall i : reg, ~ In i m2s_clob -> getr r5 i = getr r4 i) by (intros i Hi; exact (AG5 i Hi)).
    assert (E2 : getr r5 2 = at_ sp (-64)) by (rewrite AGR5 by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate); exact D2).
    assert (E8 : getr r5 8 = beg) by (rewrite AGR5, DK by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate); rewrite (AG3 8%bv) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate); exact B8).
    assert (E18 : getr r5 18 = Z_to_bv 64 endZ) by (rewrite AGR5, DK by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate); rewrite (AG3 18%bv) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate); exact B18).
    assert (E21 : getr r5 21 = Z_to_bv 64 (mt_p_shoff tm)) by (rewrite AGR5, DK by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate); rewrite (AG3 21%bv) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate); exact B21).
    assert (E19 : getr r5 19 = Z_to_bv 64 (Sh (up8 (U beg)))).
    { rewrite AGR5, D19 by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intuition discriminate). rewrite A8. unorm. reflexivity. }
    assert (AG5x : regs_agree CLX regs r5).
    { intros i Hi. rewrite (AGR5 i). apply AG4, Hi. intros Hm. apply Hi. unfold m2s_clob in Hm. cbn [In] in Hm. (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end). repeat (destruct Hm as [<-|Hm]; [(lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat first [left; reflexivity | right] |]). destruct Hm. }
    destruct (rblkD r5 E2 E8 E18 E21 AG5x) as (r6 & RUN6 & F2 & FK & AG6).
    assert (F19 : getr r6 19 = Z_to_bv 64 (Sh (up8 (U beg)))) by (rewrite FK by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact E19).
    assert (F10 : getr r6 10 = Z_to_bv 64 (Sh (down8 endZ))) by (rewrite FK by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); rewrite E10, A9; unorm; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold RMF in G in change_no_check G' end).
    destruct (Z.ltb_spec (Sh (up8 (U beg))) (Sh (down8 endZ))) as [Hlt|Hge].
    - (* [comment removed for export] *)
      destruct (rblkE1 r6 F19 F10 Hlt AG6) as (r7 & RUN7 & G1 & G10 & G11 & GK & AG7).
      assert (G2 : getr r7 2 = at_ sp (-64)) by (rewrite GK by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact F2).
      assert (STK : store_ok segs RM1 (Z_to_bv 64 (U (at_ sp (-64)) - 8)) 8 = true).
      { rewrite at_u by lia. replace (U sp + -64 - 8)%Z with (U sp + -72)%Z by lia. change (Z_to_bv 64 (U sp + -72)) with (at_ sp (-72)).
        apply RM1_ok. eapply (store_ok_sub segs mem (at_ sp (-80)) _ 80); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
      assert (DISJ : (U (Z_to_bv 64 (Sh (up8 (U beg)))) + (Sh (down8 endZ) - Sh (up8 (U beg))) <= U (at_ sp (-64)) - 8
                      \/ U (at_ sp (-64)) <= U (Z_to_bv 64 (Sh (up8 (U beg)))))%Z).
      { rewrite at_u by lia. unorm. left. lia. }
      assert (HZ : forall a : word, (U (Z_to_bv 64 (Sh (up8 (U beg)))) <= U a < U (Z_to_bv 64 (Sh (up8 (U beg)))) + (Sh (down8 endZ) - Sh (up8 (U beg))))%Z ->
                   rdn segs RM1 a 1 = Some [Z_to_bv 8 0]).
      { intros a Ha. revert Ha. unorm. intros Ha. apply rdRM1w; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. apply Rzero. lia. }
      destruct (mem_is_zero_summary segs (at_ base 66768) RM1 (Z_to_bv 64 (Sh (up8 (U beg)))) (at_ sp (-64))
                  (Sh (down8 endZ) - Sh (up8 (U beg))) rom r7 (at_ base 372) MISZ
                  ltac:(lia) ltac:(wd_ulia) ltac:(rewrite at_u; lia) STK DISJ HZ RA3 G1 G2 G10 G11)
        as (r8 & RUN8 & AG8 & K10 & K2 & K1).
      (* [comment removed for export] *)
      assert (RDs : forall (k : Z) (v : word),
                In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18);
                           (-40, getr regs 19); (-48, getr regs 20); (-56, getr regs 21)]%Z ->
                rdn segs (wbytes RM1 (at_ sp (-72)) (word_to_le_bytes 8 (at_ base 372))) (at_ sp k) 8 = Some (word_to_le_bytes 8 v)).
      { intros k v Hin. exact (proj2 (RM1_slots k v Hin) _). }
      assert (AG8x : regs_agree CLX regs r8).
      { intros i Hi. rewrite (AG8 i). apply AG7, Hi. intros Hm. apply Hi. unfold memisz_clob in Hm. cbn [In] in Hm. (lazymatch goal with |- ?G => let G' := eval unfold rip_clobx in G in change_no_check G' end). repeat (destruct Hm as [<-|Hm]; [(lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat first [left; reflexivity | right] |]). destruct Hm. }
      destruct (rblkF _ r8 372 (or_introl (conj eq_refl K10)) K2 RDs AG8x) as (r9 & RUN9 & L10 & AG9).
      exists r9. split; [|split; [exact L10 | exact AG9]].
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [|exact RUN9].
      rewrite at_u in RUN8 by lia. replace (U sp + -64 - 8)%Z with (U sp + -72)%Z in RUN8 by lia. exact RUN8.
    - (* [comment removed for export] *)
      destruct (rblkE0 r6 F19 F10 ltac:(lia) AG6) as (r7 & RUN7 & GK & AG7).
      assert (G2 : getr r7 2 = at_ sp (-64)) by (rewrite GK; exact F2).
      assert (RDs : forall (k : Z) (v : word),
                In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18);
                           (-40, getr regs 19); (-48, getr regs 20); (-56, getr regs 21)]%Z ->
                rdn segs RM1 (at_ sp k) 8 = Some (word_to_le_bytes 8 v)).
      { intros k v Hin. exact (proj1 (RM1_slots k v Hin)). }
      destruct (rblkF _ r7 376 (or_intror eq_refl) G2 RDs AG7) as (r9 & RUN9 & L10 & AG9).
      exists r9. split; [|split; [exact L10 | exact AG9]].
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      eapply msteps_trans; [exact RUN7|]. exact RUN9.
  Qed.
  End WithRegs.
End RIP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem region_clear : forall segs t, rip_tab_ok segs t ->
  forall mem rom (beg size ra sp : word) (s0b s1b : byte) (midend : word) regs,
  ripH segs t mem beg size ra sp s0b s1b midend ->
  getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = beg -> getr regs 11 = size ->
  exists r,
    msteps segs (mkst regs (rt_base t) mem rom)
                (mkst r ra (rip_mem t mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                                    (getr regs 20) (getr regs 21) beg size) rom)
    /\ getr r 10 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r rip_clob) regs r.
Proof using.
  intros segs t [TC TM TMB TZ T44 T76 T84 T112 T148 T156 T184 TB] mem rom beg size ra sp s0b s1b midend regs
         [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13] H1 H2 H10 H11.
  rewrite <- (at_0 (rt_base t)).
  exact (rip_run segs (rt_base t) (rt_m2s t) TC TM TMB TZ T44 T76 T84 T112 T148 T156 T184 TB
           mem rom beg size ra sp s0b s1b midend P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 regs H1 H2 H10 H11).
Qed.

(* [comment removed for export] *)
Lemma ps_frame_outside : forall mem (sp ra s0 s1 s2 s3 s4 s5 x : word),
  (64 <= bv_unsigned sp)%Z ->
  (bv_unsigned x < bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned x)%Z ->
  ps_frame mem sp ra s0 s1 s2 s3 s4 s5 x = mem x.
Proof using.
  intros mem sp ra s0 s1 s2 s3 s4 s5 x Hsp Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end).
  rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
Qed.

Lemma rip_mem_outside : forall t mem (sp ra s0 s1 s2 s3 s4 s5 beg size x : word),
  (80 <= bv_unsigned sp)%Z ->
  (bv_unsigned x < bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned x)%Z ->
  rip_mem t mem sp ra s0 s1 s2 s3 s4 s5 beg size x = mem x.
Proof using.
  intros t mem sp ra s0 s1 s2 s3 s4 s5 beg size x Hsp Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold rip_mem in G in change_no_check G' end).
  destruct (Z.ltb _ _).
  - rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; [| (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    apply ps_frame_outside; lia.
  - apply ps_frame_outside; lia.
Qed.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
