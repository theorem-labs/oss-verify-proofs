From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct ex_value_c ex_value_m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strtod_c ex_value_c ex_word_c ex_string_c strcmp_c bcmp_c memcpy_c ex_ws_c exvu_b exvu_w exvu_k exvu_o exvu_i exvu_l exvu_t.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import exvu_s exvu_n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

Ltac slia ::= first [ exact I | repeat split; lia1 ].

Set Default Proof Using "All".

Section EV.
Hypotheses (ESC : ex_string_contract) (EWC : ex_word_contract) (SCC : strcmp_contract) (BCC : bcmp_contract)
  (MCC : memcpy_contract) (SDC : strtod_contract) (EWS : ex_ws_contract).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (m : word -> option byte) (q v x0 i0 d dl scr lo : Z) (x : list byte) (lblk : Z -> Z -> Prop) (t : jv)
  (D : list (Z * Z)) (canary ev : word).

Local Abbreviation SP := (bv_unsigned sp).
Local Abbreviation len := (Z.of_nat (length x)).
Local Abbreviation KD := ((33 - d) * 144 + 8928).
Local Abbreviation X := (ev_X x).

Hypotheses (HTP : tp = Z_to_bv 64 0x35348) (QA : q mod 8 = 0) (QG : 0x56000 <= q)
  (RQ0 : ex_rec m q (x0 + i0) (x0 + len) d scr dl)
  (BX : bytes_at rsegs m x0 x) (X0 : 0 < x0) (XE : x0 + len < 2 ^ 62) (XL : len <= 3 * 2 ^ 20)
  (I0 : 0 <= i0 <= len) (DD : 0 <= d <= 32) (DL : dl = 0 \/ dl = 1)
  (SS0 : stk rsegs m scr (scr + len + 1)) (SG : 4096 <= scr) (SGd : scr + len + 1 <= 0x10000 \/ 0x56000 <= scr)
  (SW : scr + len + 1 <= SP - KD)
  (TV : v = 0 \/ pj_node rsegs m lblk v t D /\ Forall (fun ak => 0 < fst ak /\ fst ak mod 8 = 0) D)
  (ST0 : stk rsegs m lo SP) (LOW : lo <= SP - KD) (SA : SP mod 16 = 0) (SB : SP < 2 ^ 62)
  (SG2 : 0x56000 <= SP - KD)
  (AQX : ex_apart q 40 x0 len) (AQS : ex_apart q 40 scr (len + 1)) (AXS : ex_apart x0 len scr (len + 1))
  (AQW : ex_apart q 40 (SP - KD) KD) (AXW : ex_apart x0 len (SP - KD) KD) (AXE : ex_apart x0 len 0x352a4 4)
  (TO : v <> 0 -> ex_off v D q 40 /\ ex_off v D scr (len + 1) /\ ex_off v D (SP - KD) KD /\
                 ex_off v D 0x352a4 4)
  (GG0 : rw_cells rsegs m 0x23f98 [C8 (Z_to_bv 64 0x555b8)]) (GQ0 : rw_cells rsegs m 0x555b8 [C8 canary])
  (GE0 : rw_cells rsegs m 0x352a4 [C4 ev])
  (MI0 : mem_inv rsegs m) (TM0 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.task_mem rsegs m).

Hypothesis IHV : forall (ra' sp' gp' tp' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8'
    s9' s10' s11' t3' t4' t5' t6' : word) (F'' : bvmap 5 word) (fc'' : bv 32) (m'' : word -> option byte)
    (q' v' x0' i0' d' dl' scr' lo' : Z) (x' : list byte) (lblk' : Z -> Z -> Prop) (t' : jv) (D' : list (Z * Z))
    (canary' ev'' : word),
  (Z.to_nat (Z.of_nat (length x') - i0') < Z.to_nat (len - i0))%nat ->
  ex_value_spec ra' sp' gp' tp' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10'
    s11' t3' t4' t5' t6' F'' fc'' m'' q' v' x0' i0' d' dl' scr' lo' x' lblk' t' D' canary' ev''.

Local Abbreviation ev_W := (exvu_b.ev_W sp q d scr x).
Local Abbreviation ev_Q := (exvu_b.ev_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x t).
Local Abbreviation ev_SAVED := (exvu_b.ev_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Abbreviation ev_FI := (exvu_b.ev_FI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q x0 d scr lo x).
Local Abbreviation ev_FIN := (exvu_b.ev_FIN v i0 d dl scr x t).
Local Abbreviation ev_D0 := (exvu_b.ev_D0 v dl t).
Local Abbreviation ev_VV := (exvu_b.ev_VV v t).
Local Abbreviation ev_US := exvu_b.ev_US.
Local Abbreviation ev_DI := (exvu_b.ev_DI v dl t).
Local Abbreviation ev_KID := (exvu_b.ev_KID m v lblk t D).
Local Abbreviation ev_HEAD := (exvu_b.ev_HEAD sp gp tp q).
Local Abbreviation ev_tm := (exvu_b.ev_tm ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_bx := (exvu_b.ev_bx ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_gg := (exvu_b.ev_gg ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_gq := (exvu_b.ev_gq ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_off_out := (exvu_b.ev_off_out ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_tree := (exvu_b.ev_tree ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_epi := (exvu_b.ev_epi ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_vr := (exvu_b.ev_vr ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_find_rw := (exvu_b.strlit_find_rw ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_wv_mrd := (exvu_b.strlit_wv_mrd ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_stk_mono := (exvu_b.strlit_stk_mono ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_prefixb := (exvu_b.strlit_prefixb ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_match := (exvu_b.strlit_match ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_lit_tag := (exvu_b.strlit_lit_tag ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_v_tr := (exvu_b.ev_v_tr ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_kid_ok := (exvu_b.ev_kid_ok ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_US_app := (exvu_b.ev_US_app ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation close_dl := (exvu_b.close_dl ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_DI_next := (exvu_b.ev_DI_next ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_skip_map := (exvu_b.objn_skip_map ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_X_skip := (exvu_b.objn_X_skip ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_stk_fill := (exvu_b.objn_stk_fill ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_name_nil := (exvu_b.objn_name_nil ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_name_nq := (exvu_b.objn_name_nq ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_name_str0 := (exvu_b.objn_name_str0 ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_name_str := (exvu_b.objn_name_str ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_skip_hd := (exvu_b.ev_skip_hd ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_v8 := (exvu_b.ev_v8 ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_D8 := (exvu_b.ev_D8 ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_ws := (exvu_w.ev_ws ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_lit := (exvu_t.ev_lit ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_str := (CF.exvu_s.ev_str ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_cont := (exvu_l.ev_cont ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_num := (CF.exvu_n.ev_num ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).

Ltac ap H := let H' := fresh "A" in pose proof H as H'; unfold ex_apart in H'.
Ltac fi_pack := unfold exvu_b.ev_FI; rewrite ?ev_rec_iff; repeat (first [ eassumption | apply conj | eexists ]).
Ltac fi_open HFI := let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in let FR := fresh "FR" in
  let ST := fresh "ST" in let EV := fresh "EV" in let REC := fresh "REC" in let DL' := fresh "DL'" in
  let FRM := fresh "FRM" in let FK := fresh "FK" in let ev' := fresh "ev'" in
  pose proof HFI as (MU & WM & MI & FR & ST & (ev' & EV) & REC & DL' & FRM & FK);
  apply ev_rec_iff in REC; destruct REC as (RP & RE & RD & RS & RF); unfold exvu_b.ev_W in MU; unfold exvu_b.ev_SAVED in FR.
Ltac ev_fipack := try unfold ev_hid in *; fi_pack.
Ltac trapx H := zify_cond H; revert H; rewrite ?ev_sgn, ?unsigned_lit by lia1; intro H;
  repeat match type of H with
  | context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; cbn [Z.b2z] in H; rewrite ?Z.shiftr_div_pow2 in H by lia;
  first [lia1 | Z.div_mod_to_equations; lia1].

Lemma ev_disp : forall i1 (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) m' j (fc' : bv 32) (F' : bvmap 5 word),
  ev_FI m' j i1 d dl fc' F' -> stk rsegs m' scr (scr + len + 1) -> i0 <= i1 <= len -> X i1 = skip (X i0) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 v) y10 y11 y12 y13
    y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x14754) fc' None m'
    (seg_rom rsegs)).
Proof.
  intros i1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 m' j fc' F' HFI SS Hi HX.
  assert (LJ : length j = 40%nat) by (destruct HFI as (_ & _ & _ & (((Lj & _) & _) & _) & _); exact Lj).
  destruct (ev_jl_ex j LJ) as (w0 & w8 & w16 & w24 & w32 & ->).
  assert (HV : ex_V d (X i0) = ex_V d (X i1)) by (rewrite HX; symmetry; apply ev_V_skip).
  pose proof HFI as HFI0.
  fi_open HFI0.
  pose proof (ev_bx m' MU) as BXm.
  pose proof (ev_al8 q QA) as HLq.
  pose proof (ev_rw_wr _ _ _ RP) as (QR1 & QR2 & _). cbn [cells_size csize Nat.add] in QR2.
  zstep. zstep. if_cases HT; [exfalso; trapx HT|].
  zstep. zstep. zstep. zstep.
  if_cases H1; zify_cond H1.
  { eapply ev_epi; [exact HFI|]. unfold exvu_b.ev_FIN. rewrite HV, (ev_X_end x i1), ex_V_nil by lia1.
    split; [reflexivity|]. lia1. }
  zstep. if_cases HT2; [exfalso; trapx HT2|].
  assert (Hi1 : 0 <= i1 < len) by lia1.
  pose proof (ev_read_x m' x0 x i1 BXm Hi1) as RX.
  pose proof (ev_X_cons x i1 Hi1) as XC.
  remember (nth (Z.to_nat i1) x (Z_to_bv 8 0)) as c eqn:Ec.
  pose proof (ev_byte_range c) as Rc.
  assert (WSc : ws (bv_unsigned c) = false).
  { apply (ev_skip_hd (X i0) _ (X (i1 + 1))). rewrite <- HX. exact XC. }
  zstep. zstep. zstep.
  if_cases H2; zify_cond H2; rewrite ?ev_sgn in H2 by lia1.
  - zstep. zstep.
    if_cases H3; zify_cond H3.
    + assert (C : bv_unsigned c = 110) by (revert H3; rewrite ?unsigned_lit by lia1; lia1).
      zstep. zstep. zstep. zstep. zstep.
      eapply (ev_lit 0x102ed 0 (map (Z_to_bv 8) w_null) w_null JNull i1); [exact HFI|lia1|right; right; split; reflexivity|
        reflexivity|repeat constructor; lia1|discriminate|reflexivity| |].
      * intros t' Ht'. destruct t'; cbn in Ht'; first [reflexivity|discriminate].
      * rewrite HV, XC, C, ex_V_null. reflexivity.
    + zstep. zstep.
      if_cases H4; zify_cond H4.
      * assert (C : bv_unsigned c = 116) by (revert H4; rewrite ?unsigned_lit by lia1; lia1).
        zstep. zstep. zstep. zstep.
        eapply (ev_lit 0x10349 2 (map (Z_to_bv 8) w_true) w_true JTrue i1); [exact HFI|lia1|left; split; reflexivity|
          reflexivity|repeat constructor; lia1|discriminate|reflexivity| |].
        -- intros t' Ht'. destruct t'; cbn in Ht'; first [reflexivity|discriminate].
        -- rewrite HV, XC, C, ex_V_true. reflexivity.
      * zstep. zstep.
        if_cases H5; zify_cond H5.
        -- eapply (ev_num (bv_unsigned c) i1); [exact HFI|exact SS|lia1|exact XC|lia1|exact WSc|
             revert H5; rewrite ?unsigned_lit by lia1; lia1|lia1|lia1|
             revert H4; rewrite ?unsigned_lit by lia1; lia1|lia1|
             revert H3; rewrite ?unsigned_lit by lia1; lia1|exact HV].
        -- assert (C : bv_unsigned c = 123) by (revert H5; rewrite ?unsigned_lit by lia1; lia1).
           zstep. zstep.
           if_cases H6; zify_cond H6; [|exfalso; revert H6; rewrite ?unsigned_lit by lia1; lia1].
           zstep.
           rewrite C in XC |- *.
           eapply (ev_cont true i1); [exact HFI|exact SS|lia1|exact XC|exact HV].
  - zstep. zstep.
    if_cases H3; zify_cond H3.
    + assert (C : bv_unsigned c = 34) by (revert H3; rewrite ?unsigned_lit by lia1; lia1).
      rewrite C in XC.
      eapply ev_str; [exact HFI|exact SS|lia1|exact XC|exact HV].
    + zstep. zstep.
      if_cases H4; zify_cond H4.
      * assert (C : bv_unsigned c = 91) by (revert H4; rewrite ?unsigned_lit by lia1; lia1).
        zstep. zstep.
        if_cases H5; zify_cond H5; [exfalso; revert H5; rewrite ?unsigned_lit by lia1; lia1|].
        zstep. zstep.
        rewrite C in XC |- *.
        eapply (ev_cont false i1); [exact HFI|exact SS|lia1|exact XC|exact HV].
      * zstep. zstep.
        if_cases H5; zify_cond H5.
        -- eapply (ev_num (bv_unsigned c) i1); [exact HFI|exact SS|lia1|exact XC|lia1|exact WSc|lia1|
             revert H4; rewrite ?unsigned_lit by lia1; lia1|
             revert H3; rewrite ?unsigned_lit by lia1; lia1|lia1|
             revert H5; rewrite ?unsigned_lit by lia1; lia1|lia1|exact HV].
        -- assert (C : bv_unsigned c = 102) by (revert H5; rewrite ?unsigned_lit by lia1; lia1).
           zstep. zstep. zstep. zstep. zstep.
           eapply (ev_lit 0x10298 1 (map (Z_to_bv 8) w_false) w_false JFalse i1); [exact HFI|lia1|
             right; left; split; reflexivity|reflexivity|repeat constructor; lia1|discriminate|reflexivity| |].
           ++ intros t' Ht'. destruct t'; cbn in Ht'; first [reflexivity|discriminate].
           ++ rewrite HV, XC, C, ex_V_false. reflexivity.
Qed.


Lemma ev_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32), frm0 fc ->
  evt rsegs ev_Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
    s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14710) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc FRM.
  match goal with |- evt ?S ?Q (MS ?R ?F' ?pc ?fc' ?rv m ?ro) =>
    enough (G : forall m1, m1 = m -> evt S Q (MS R F' pc fc' rv m1 ro)) by (apply G; reflexivity) end.
  intros m1 E1.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ev_vr as VR.
  assert (MU : munch ev_W m m1) by (rewrite E1; apply munch_refl).
  assert (WM : wmono rsegs m m1) by (rewrite E1; apply wmono_refl).
  unfold exvu_b.ev_W in MU.
  pose proof SS0 as SS. pose proof BX as BXm. pose proof MI0 as MI. pose proof GE0 as EV. pose proof ST0 as ST1.
  pose proof RQ0 as RQ.
  rewrite <- E1 in SS, BXm, MI, EV, ST1, RQ.
  destruct (stk_carve rsegs m1 lo SP 144 ST1 ltac:(lia1)) as [ST [junk FR]]. clear ST1.
  replace (SP - Z.of_nat 144) with (SP + -144) in ST, FR by lia1.
  apply ev_rec_iff in RQ. destruct RQ as (RP & RE & RD & RS & RF).
  ap AQW. ap AXW. ap AQS. ap AXS. ap AQX.
  do 14 zstep.
  zstep. zstep. zstep.
  eapply (ev_ws i0 0x14754); [lia1|reflexivity|lia1|fi_pack|].
  intros i1 m'' z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 FI' Hr HXs MU' WM'.
  eapply (ev_disp i1); [exact FI'| |lia1|exact HXs].
  eapply stk_transport_disjoint; [exact SS|exact MU'|exact WM'|cbn [disjoint_from]; split; [lia1|exact I]].
Qed.

End EV.
