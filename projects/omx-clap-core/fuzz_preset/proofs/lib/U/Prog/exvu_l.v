From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct ex_value_c ex_value_m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strtod_c ex_value_c ex_word_c ex_string_c strcmp_c bcmp_c memcpy_c ex_ws_c exvu_b exvu_w exvu_k exvu_o exvu_i.
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
Local Abbreviation ev_close := (exvu_k.ev_close ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_colon := (exvu_o.objn_colon ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_after := (exvu_o.objn_after ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_key := (exvu_o.objn_key ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_quote := (exvu_o.objn_quote ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_obj_name := (exvu_o.ev_obj_name ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_item := (exvu_i.ev_item ESC EWC SCC BCC MCC SDC EWS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).

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

Ltac zshr := repeat match goal with |- context [Z.shiftr ?e ?k] =>
  lazymatch k with 64 => idtac | 63 => idtac end;
  replace (Z.shiftr e k) with 0 by (rewrite ?ev_sgn, ?unsigned_lit by lia1; rewrite Z.shiftr_div_pow2 by lia;
    symmetry; apply Z.div_small; lia1) end.

Lemma ev_loop : forall (k : nat) (o : bool) i (n cap : nat) acc vv dlc (w0 w24 w32 : word) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y27 y28 y29 y30 y31 : word) m' fc' F',
  Z.to_nat (len - i) = k -> i0 < i <= len -> d + 1 <= 32 ->
  ev_FI m' (ev_jl w0 (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 (closer o)) w24 w32) i (d + 1) dlc fc' F' -> stk rsegs m' scr (scr + len + 1) ->
  ev_VV o vv -> n = length acc -> Z.of_nat n < i -> ev_US o (rev acc) -> ev_DI o vv n (rev acc) dlc ->
  ex_V d (X i0) = ex_L (S (Z.to_nat d)) o n cap acc (X i) ->
  evt rsegs ev_Q (ev_HEAD o vv n y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y27 y28 y29 y30 y31 F' fc' m').
Proof.
  induction k as [k IHk] using lt_wf_ind.
  intros o i n cap acc vv dlc w0 w24 w32 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y27 y28 y29 y30 y31 m' fc' F' Hk Hi Hd HFI SS VV Hn Hni US DI HM.
  rewrite ex_L_step in HM. replace (Z.of_nat (S (Z.to_nat d))) with (d + 1) in HM by lia1.
  assert (KN : forall nm u, ev_US o (rev acc ++ [(nm, JNull)]) -> forall i' m'' dl'' (F'' : bvmap 5 word) (fc'' : bv 32)
      (w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 : word),
     i < i' <= len -> ev_FI m'' (ev_jl w0 (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 (closer o)) w24 w32) i' (d + 1) dl'' fc'' F'' -> stk rsegs m'' scr (scr + len + 1) ->
     ev_DI o vv (S n) (rev acc ++ [(nm, u)]) dl'' ->
     ex_V d (X i0) = ex_L (S (Z.to_nat d)) o (S n) (ex_cap n cap) ((nm, u) :: acc) (X i') ->
     evt rsegs ev_Q (ev_HEAD o vv (S n) w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 F'' fc'' m'')).
  { intros nm u USn i' m'' dl'' F'' fc'' w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 Hi' FI' SS' DI' HM'.
    eapply (IHk (Z.to_nat (len - i')) ltac:(lia1) o i' (S n) (ex_cap n cap) ((nm, u) :: acc) vv dl'' w0 w24 w32);
      [reflexivity|lia1|exact Hd|exact FI'|exact SS'|exact VV|cbn [length]; lia1|lia1| | |exact HM'].
    - cbn [rev]. eapply ev_US_app. exact USn.
    - cbn [rev]. exact DI'. }
  pose proof ev_vr as VR.
  unfold exvu_b.ev_HEAD.
  destruct DI as (DIr & DIi).
  destruct (Z.eqb_spec vv 0) as [V0|V0].
  - subst vv.
    assert (KID : ev_KID 0 n 0 0) by (left; split; [reflexivity|split; [reflexivity|left; reflexivity]]).
    fi_open HFI.
    zstep. zstep. zstep.
    destruct o.
    + if_cases HB; zify_cond HB; [lia1|].
      eapply (ev_obj_name i n 0 dlc 0 0 w0 w24 w32); [fi_pack|exact SS|lia1|exact Hd|lia1|exact VV|exact KID|exact DIr| |].
      * intro HN. rewrite HM, HN. reflexivity.
      * intros nm i' m'' dlB z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HN Hi' FI' SS' DLB DLBi.
        rewrite HN in HM.
        eapply (ev_item true i' n cap acc 0 dlB 0 0 nm w0 w24 w32); [exact FI'|exact SS'|lia1|exact Hd|exact VV|exact KID|
          exact DLB|exact Hn|lia1| |intro; discriminate|exact HM|].
        -- intros u dlC H1 H2. eapply (ev_DI_next true 0 n (rev acc) dlc dlc 0 0 nm u dlB dlC);
             [exact VV|rewrite length_rev; exact Hn|split; assumption|exact KID|intro; discriminate| |exact DLBi|
              exact H1|exact H2].
           split; [intro H; left; exact H|intros [H|(H & _)]; [exact H|lia1]].
        -- intros i'' m3 dl3 u F3 fc3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 H1 H2 H3 H4 H5.
           exact (KN nm u (fun H => ltac:(discriminate)) i'' m3 dl3 F3 fc3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 ltac:(lia1) H2 H3 H4 H5).
    + if_cases HB; zify_cond HB; [|lia1].
      cbn [ex_name] in HM.
      eapply (ev_item false i n cap acc 0 dlc 0 0 [] w0 w24 w32); [fi_pack|exact SS|lia1|exact Hd|exact VV|exact KID|
        exact DIr|exact Hn|lia1| | |exact HM|].
      * intros u dlC H1 H2. eapply (ev_DI_next false 0 n (rev acc) dlc dlc 0 0 [] u dlc dlC);
          [exact VV|rewrite length_rev; exact Hn|split; assumption|exact KID|intro; reflexivity| | |exact H1|exact H2].
        -- split; [intro H; left; exact H|intros [H|(H & _)]; [exact H|lia1]].
        -- split; [intro H; left; exact H|intros [H|(H & _)]; [exact H|lia1]].
      * intro Ho. apply Forall_app. split; [exact (US Ho)|constructor; [reflexivity|constructor]].
      * intros i'' m3 dl3 u F3 fc3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 H1 H2 H3 H4 H5.
        eapply (KN [] u); [|exact H1|exact H2|exact H3|exact H4|exact H5].
        intro Ho. apply Forall_app. split; [exact (US Ho)|constructor; [reflexivity|constructor]].
  - pose proof VV as VV0.
    destruct VV as [(E0 & _)|(Evv & Hv & Htag)]; [contradiction|]. subst vv.
    pose proof TV as TV'. destruct TV' as [E|[TN FD]]; [contradiction|].
    destruct (ev_node_cont _ _ _ _ _ o TN Htag) as (num & kids & keys & cap0 & HH & KIDS).
    destruct HH as (RW & U32 & U64n & U64s & U64k & U64y & U64c & U64cap).
    destruct RW as (_ & (Sa & Sb & _)).
    fi_open HFI. ap AQW. ap AQX.
    assert (DL1 : 1 = 0 \/ 1 = 1) by (right; reflexivity).
    assert (RC : ov_read_bytes rsegs m' (wa (v + 40)) 8 = Some (le8 (Z_to_bv 64 (Z.of_nat (length (tkids t)))))).
    { apply ev_u64_rd. destruct U64c as [Hr B]. split; [exact Hr|].
      apply (ev_v_tr Hv m' _ _ MU B); [lia1|rewrite length_le8; lia1]. }
    pose proof U64c as (Rcnt & _).
    zstep. zstep.
    if_cases H1; zify_cond H1.
    + assert (DLA : (1 = 1 <-> dlc = 1 \/ (v <> 0 /\ (length (tkids t) <= n)%nat))) by
        (split; [intros _; right; split; [exact Hv|lia1]|intros _; reflexivity]).
      assert (KID : ev_KID v n 0 0) by (left; split; [reflexivity|split; [reflexivity|right; lia1]]).
      zstep. zstep. zstep. zstep. zstep.
      destruct o.
      * if_cases HB; zify_cond HB; [|lia1].
        eapply (ev_obj_name i n v 1 0 0 w0 w24 w32); [fi_pack|exact SS|lia1|exact Hd|lia1|exact VV0|exact KID|
          right; reflexivity| |].
        -- intro HN. rewrite HM, HN. reflexivity.
        -- intros nm i' m'' dlB z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HN Hi' FI' SS' DLB DLBi.
           rewrite HN in HM.
           eapply (ev_item true i' n cap acc v dlB 0 0 nm w0 w24 w32); [exact FI'|exact SS'|lia1|exact Hd|exact VV0|
             exact KID|exact DLB|exact Hn|lia1| |intro; discriminate|exact HM|].
           ++ intros u dlC E1 E2. eapply (ev_DI_next true v n (rev acc) dlc 1 0 0 nm u dlB dlC);
                [exact VV0|rewrite length_rev; exact Hn|split; assumption|exact KID|intro; discriminate|
                 exact DLA|exact DLBi|exact E1|exact E2].
           ++ intros i'' m3 dl3 u F3 fc3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 E1 E2 E3 E4 E5.
              exact (KN nm u (fun H => ltac:(discriminate)) i'' m3 dl3 F3 fc3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 ltac:(lia1) E2 E3 E4 E5).
      * if_cases HB; zify_cond HB; [lia1|]. zstep.
        cbn [ex_name] in HM.
        eapply (ev_item false i n cap acc v 1 0 0 [] w0 w24 w32); [fi_pack|exact SS|lia1|exact Hd|exact VV0|exact KID|
          right; reflexivity|exact Hn|lia1| | |exact HM|].
        -- intros u dlC E1 E2. eapply (ev_DI_next false v n (rev acc) dlc 1 0 0 [] u 1 dlC);
             [exact VV0|rewrite length_rev; exact Hn|split; assumption|exact KID|intro; reflexivity|
              exact DLA| |exact E1|exact E2].
           split; [intro H; left; exact H|intros [H|(H & _)]; [exact H|lia1]].
        -- intro Ho. apply Forall_app. split; [exact (US Ho)|constructor; [reflexivity|constructor]].
        -- intros i'' m3 dl3 u F3 fc3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 E1 E2 E3 E4 E5.
           eapply (KN [] u); [|exact E1|exact E2|exact E3|exact E4|exact E5].
           intro Ho. apply Forall_app. split; [exact (US Ho)|constructor; [reflexivity|constructor]].
    + destruct (KIDS n ltac:(lia1)) as (Hncap & HinK & (Dn & TNk & InclD) & KEYS).
      assert (KP : 0 < kids /\ kids mod 8 = 0) by (rewrite Forall_forall in FD; exact (FD _ HinK)).
      assert (RK : ov_read_bytes rsegs m' (wa (v + 24)) 8 = Some (le8 (Z_to_bv 64 kids))).
      { apply ev_u64_rd. destruct U64k as [Hr B]. split; [exact Hr|].
        apply (ev_v_tr Hv m' _ _ MU B); [lia1|rewrite length_le8; lia1]. }
      pose proof U64k as (Rk & _).
      destruct (ev_hdr _ _ _ _ _ TNk) as (? & ? & ? & ? & ? & ? & ((_ & (Ska & Skb & _)) & _)).
      assert (SH3 : Z.shiftl (Z.of_nat n) 3 = 8 * Z.of_nat n)
        by (rewrite Z.shiftl_mul_pow2 by lia1; change (2 ^ 3) with 8; lia1).
      assert (SH6 : Z.shiftl (Z.of_nat n) 6 = 64 * Z.of_nat n)
        by (rewrite Z.shiftl_mul_pow2 by lia1; change (2 ^ 6) with 64; lia1).
      zstep. zstep. zstep. zstep. rewrite ?SH3, ?SH6.
      zstep. zstep. zstep. zstep. if_cases HT1; [exfalso; trapx HT1|].
      zstep. if_cases HT2; [exfalso; trapx HT2|].
      zstep. zstep. zstep. zshr. zstep. zstep. zstep. if_cases HT3; [exfalso; trapx HT3|].
      zstep. if_cases HT4; [exfalso; trapx HT4|].
      zstep. zstep.
      assert (KID : ev_KID v n (kids + 56 * Z.of_nat n) 1).
      { right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hv|]. split; [lia1|]. split; [lia1|].
        exists kids, (56 * cap0), Dn. split; [exact HinK|]. split; [lia1|]. split; [lia1|]. split; [exact TNk|exact InclD]. }
      assert (DLA : dlc = 1 <-> dlc = 1 \/ (v <> 0 /\ (length (tkids t) <= n)%nat))
        by (split; [intro H; left; exact H|intros [H|(_ & H)]; [exact H|lia1]]).
      zstep.
      destruct o.
      * if_cases HB; zify_cond HB; [|lia1].
        eapply (ev_obj_name i n v dlc (kids + 56 * Z.of_nat n) 1 w0 w24 w32); [fi_pack|exact SS|lia1|exact Hd|lia1|
          exact VV0|exact KID|exact DIr| |].
        -- intro HN. rewrite HM, HN. reflexivity.
        -- intros nm i' m'' dlB z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HN Hi' FI' SS' DLB DLBi.
           rewrite HN in HM.
           eapply (ev_item true i' n cap acc v dlB (kids + 56 * Z.of_nat n) 1 nm w0 w24 w32); [exact FI'|exact SS'|lia1|
             exact Hd|exact VV0|exact KID|exact DLB|exact Hn|lia1| |intro; discriminate|exact HM|].
           ++ intros u dlC E1 E2. eapply (ev_DI_next true v n (rev acc) dlc dlc (kids + 56 * Z.of_nat n) 1 nm u dlB dlC);
                [exact VV0|rewrite length_rev; exact Hn|split; assumption|exact KID|intro; discriminate|
                 exact DLA|exact DLBi|exact E1|exact E2].
           ++ intros i'' m3 dl3 u F3 fc3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 E1 E2 E3 E4 E5.
              exact (KN nm u (fun H => ltac:(discriminate)) i'' m3 dl3 F3 fc3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 ltac:(lia1) E2 E3 E4 E5).
      * if_cases HB; zify_cond HB; [lia1|]. zstep.
        cbn [ex_name] in HM.
        eapply (ev_item false i n cap acc v dlc (kids + 56 * Z.of_nat n) 1 [] w0 w24 w32); [fi_pack|exact SS|lia1|exact Hd|
          exact VV0|exact KID|exact DIr|exact Hn|lia1| | |exact HM|].
        -- intros u dlC E1 E2. eapply (ev_DI_next false v n (rev acc) dlc dlc (kids + 56 * Z.of_nat n) 1 [] u dlc dlC);
             [exact VV0|rewrite length_rev; exact Hn|split; assumption|exact KID|intro; reflexivity|
              exact DLA| |exact E1|exact E2].
           split; [intro H; left; exact H|intros [H|(_ & H)]; [exact H|exfalso; apply H; apply ev_fst_arr; exact Htag]].
        -- intro Ho. apply Forall_app. split; [exact (US Ho)|constructor; [reflexivity|constructor]].
        -- intros i'' m3 dl3 u F3 fc3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w19 w27 w28 w29 w30 w31 E1 E2 E3 E4 E5.
           eapply (KN [] u); [|exact E1|exact E2|exact E3|exact E4|exact E5].
           intro Ho. apply Forall_app. split; [exact (US Ho)|constructor; [reflexivity|constructor]].
Qed.

Lemma ev_init : forall (o : bool) iw vv dlA (w0 w8 w24 w32 : word) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) m3 fc' F',
  ev_FI m3 (ev_jl w0 w8 (Z_to_bv 64 (closer o)) w24 w32) iw (d + 1) dlA fc' F' -> stk rsegs m3 scr (scr + len + 1) -> i0 < iw <= len -> d + 1 <= 32 ->
  ev_VV o vv -> ev_DI o vv 0 [] dlA -> ex_V d (X i0) = ex_L (S (Z.to_nat d)) o 0 0 [] (X iw) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 vv) y10 y11 y12
      y13 y14 y15 y16 y17 (Z_to_bv 64 (-1)) y19 (Z_to_bv 64 (if o then 123 else 91)) y21 y22 y23
      y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x14a70) fc' None m3 (seg_rom rsegs)).
Proof.
  intros o iw vv dlA w0 w8 w24 w32 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 m3 fc' F' HFI SS Hi Hd VV DI HM.
  fi_open HFI. ap AQW.
  apply (proj1 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
  do 9 zstep.
  apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
  pose proof (ev_loop (Z.to_nat (len - iw)) o iw 0 0 [] vv dlA w0 w24 w32) as LP. unfold exvu_b.ev_HEAD in LP.
  zstep.
  if_cases HB; zify_cond HB.
  - assert (V0 : vv = 0) by (destruct VV as [(-> & _)|(-> & Hv & _)]; [reflexivity|];
      pose proof ev_vr; revert HB; rewrite ?unsigned_lit by lia1; lia1).
    subst vv. rewrite Z.eqb_refl in LP.
    eapply LP; [reflexivity|lia1|lia1|fi_pack|exact SS|exact VV|reflexivity|cbn; lia1|intro; constructor|exact DI|
      exact HM].
  - assert (V0 : vv <> 0) by (intro E0; subst vv; apply HB; reflexivity).
    rewrite (proj2 (Z.eqb_neq _ _) V0) in LP.
    eapply LP; [reflexivity|lia1|lia1|fi_pack|exact SS|exact VV|reflexivity|cbn; lia1|intro; constructor|exact DI|
      exact HM].
Qed.

Lemma ev_open : forall (o : bool) i1 vv dlA (w0 w8 w24 w32 : word) (y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) m' fc' F',
  ev_FI m' (ev_jl w0 w8 (Z_to_bv 64 (closer o)) w24 w32) i1 (d + 1) dlA fc' F' -> stk rsegs m' scr (scr + len + 1) -> i0 <= i1 < len -> d + 1 <= 32 ->
  ev_VV o vv -> ev_DI o vv 0 [] dlA ->
  ex_V d (X i0) = match skip (X (i1 + 1)) with
    | c :: r => if c =? closer o then Some (mk o [], r) else ex_L (S (Z.to_nat d)) o 0 0 [] (c :: r)
    | [] => None
    end ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 vv) y10 (Z_to_bv 64 (x0 + i1)) y12
      y13 y14 y15 y16 y17 (Z_to_bv 64 (-1)) y19 (Z_to_bv 64 (if o then 123 else 91)) y21 y22 y23
      y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x149d4) fc' None m' (seg_rom rsegs)).
Proof.
  intros o i1 vv dlA w0 w8 w24 w32 y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 m' fc' F' HFI SS Hi Hd VV DI HM.
  fi_open HFI. ap AQW. ap AQX. ap AQS.
  zstep. zstep. zstep. if_cases HT; [exfalso; trapx HT|].
  zstep.
  replace (x0 + i1 + 1) with (x0 + (i1 + 1)) in * by lia1.
  zstep. zstep.
  eapply (ev_ws (i1 + 1) 0x149ec); [lia1|reflexivity|lia1|fi_pack|].
  intros iw m3 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 FI3 Hiw HX MU3 WM3.
  assert (SS3 : stk rsegs m3 scr (scr + len + 1)).
  { eapply stk_transport_disjoint; [exact SS|exact MU3|exact WM3|cbn [disjoint_from]; split; [lia1|exact I]]. }
  rewrite <- HX in HM.
  clear RP RE RD RS RF FR. fi_open FI3. ap AQW. ap AQX.
  zstep. zstep. zstep.
  if_cases H1; zify_cond H1.
  { eapply ev_init; [fi_pack|exact SS3|lia1|exact Hd|exact VV|exact DI|].
    rewrite HM, (ev_X_end x iw) by lia1. symmetry. apply ev_L_nil. }
  zstep. if_cases HT2; [exfalso; trapx HT2|].
  pose proof (ev_bx m3 (proj1 FI3)) as BX3.
  pose proof (ev_read_x m3 x0 x iw BX3 ltac:(lia1)) as RX.
  pose proof (ev_X_cons x iw ltac:(lia1)) as XC.
  remember (nth (Z.to_nat iw) x (Z_to_bv 8 0)) as c eqn:Ec.
  pose proof (ev_byte_range c) as Rc.
  rewrite XC in HM.
  apply (proj1 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
  zstep. zstep. zstep.
  if_cases H2; zify_cond H2.
  - apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
    eapply ev_init; [fi_pack|exact SS3|lia1|exact Hd|exact VV|exact DI|]. rewrite HM, XC.
    rewrite (proj2 (Z.eqb_neq _ _)) by (destruct o; cbn in H2 |- *; lia1). reflexivity.
  - zstep. zstep. if_cases HT3; [exfalso; trapx HT3|].
    zstep. zstep. zstep. zstep.
    apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
    replace (x0 + iw + 1) with (x0 + (iw + 1)) in * by lia1.
    eapply (ev_close o 0 [] vv dlA (iw + 1)); [fi_pack|exact SS3|lia1|lia1|exact VV|reflexivity|cbn; lia1|
      intro; constructor|exact DI|].
    rewrite HM. rewrite (proj2 (Z.eqb_eq _ _)) by (destruct o; cbn in H2 |- *; lia1). reflexivity.
Qed.

Lemma ev_cont : forall (o : bool) i1 (w0 w8 w16 w24 w32 : word) (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) m' fc' F',
  ev_FI m' (ev_jl w0 w8 w16 w24 w32) i1 d dl fc' F' -> stk rsegs m' scr (scr + len + 1) -> i0 <= i1 < len ->
  X i1 = (if o then 123 else 91) :: X (i1 + 1) -> ex_V d (X i0) = ex_V d (X i1) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 v) (Z_to_bv 64 (closer o))
    (Z_to_bv 64 (x0 + i1)) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (-1)) y19 (Z_to_bv 64 (if o then 123 else 91)) y21 y22 y23
    y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x1498c) fc' None m' (seg_rom rsegs)).
Proof.
  intros o i1 w0 w8 w16 w24 w32 y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 m' fc' F' HFI SS Hi XC HV.
  assert (HV2 : ex_V d (X i0) = if 32 <? d + 1 then None else
     match skip (X (i1 + 1)) with
     | c :: r => if c =? closer o then Some (mk o [], r) else ex_L (S (Z.to_nat d)) o 0 0 [] (c :: r)
     | [] => None
     end).
  { rewrite HV, XC. rewrite ex_V_open by (lia1 || (destruct o; [left|right]; reflexivity)). destruct o; reflexivity. }
  fi_open HFI. ap AQW. ap AQX.
  pose proof ev_vr as VR.
  apply (proj1 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
  zstep.
  apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
  zstep. rewrite ?ev_sx32 by lia1.
  zstep. rewrite ?Z.add_0_r, ?ev_swrap32 by lia1.
  zstep. if_cases HT; [exfalso; trapx HT|].
  zstep. zstep.
  zstep. if_cases H1; zify_cond H1; rewrite ?ev_sgn in H1 by lia1.
  { eapply ev_epi; [fi_pack|]. unfold exvu_b.ev_FIN. rewrite HV2, (proj2 (Z.ltb_lt _ _)) by lia1. split; [reflexivity|lia1]. }
  rewrite (proj2 (Z.ltb_ge _ _)) in HV2 by lia1.
  zstep.
  if_cases H2; zify_cond H2.
  - assert (V0 : v = 0) by (revert H2; rewrite ?unsigned_lit by lia1; lia1).
    replace (Z_to_bv 64 v) with (Z_to_bv 64 0) by (rewrite V0; reflexivity).
    eapply (ev_open o i1 0 dl w0 w8 w24 w32); [fi_pack|exact SS|lia1|lia1| |split; [exact DL|]|exact HV2].
    + left. split; [reflexivity|left; exact V0].
    + unfold exvu_b.ev_D0. split; [intro H; left; left; exact H|]. intros [[H|(H & _)]|(H & _)]; [exact H|contradiction|lia1].
  - assert (V0 : v <> 0) by (intro E0; rewrite E0 in H2; apply H2; reflexivity).
    destruct TV as [E0|[TN FD]]; [contradiction|].
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (ev_tree mm V0 MU) as TN0 end.
    destruct (ev_hdr _ _ _ _ _ TN0) as (num & str & kids & keys & nn & cap & HH).
    destruct HH as (_ & U32 & _).
    pose proof (ev_u32_rd _ _ _ U32) as RT.
    pose proof (ev_tag_range t) as TR.
    pose proof (ev_al8 v (ev_v8 V0)) as HL.
    zstep. zstep. if_cases HT2; [exfalso; trapx HT2|].
    zstep. rewrite ?ev_sx32 by lia1.
    destruct o.
    + zstep. zstep. zstep. zstep.
      if_cases H3; zify_cond H3; cbn in H3.
      * eapply (ev_open true i1 v dl w0 w8 w24 w32); [fi_pack|exact SS|lia1|lia1|right; split; [reflexivity|split; [exact V0|]]|
          split; [exact DL|]|exact HV2].
        -- cbn. lia1.
        -- unfold exvu_b.ev_D0. cbn [Z.b2z]. split; [intro H; left; left; exact H|].
           intros [[H|(_ & H)]|(_ & jj & Hjj & _)]; [exact H|lia1|lia].
      * zstep. zstep. zstep. assert (DL1 : 1 = 0 \/ 1 = 1) by (right; reflexivity).
        eapply (ev_open true i1 0 1 w0 w8 w24 w32); [fi_pack|exact SS|lia1|lia1|left; split; [reflexivity|right; cbn; lia1]|
          split; [right; reflexivity|]|exact HV2].
        unfold exvu_b.ev_D0. cbn [Z.b2z]. split; [intros _; left; right; split; [exact V0|lia1]|intros _; reflexivity].
    + zstep. zstep. zstep. zstep.
      if_cases H3; zify_cond H3; cbn in H3.
      * eapply (ev_open false i1 v dl w0 w8 w24 w32); [fi_pack|exact SS|lia1|lia1|right; split; [reflexivity|split; [exact V0|]]|
          split; [exact DL|]|exact HV2].
        -- cbn. lia1.
        -- unfold exvu_b.ev_D0. cbn [Z.b2z]. split; [intro H; left; left; exact H|].
           intros [[H|(_ & H)]|(_ & jj & Hjj & _)]; [exact H|lia1|lia].
      * zstep. zstep. zstep. assert (DL1 : 1 = 0 \/ 1 = 1) by (right; reflexivity).
        eapply (ev_open false i1 0 1 w0 w8 w24 w32); [fi_pack|exact SS|lia1|lia1|left; split; [reflexivity|right; cbn; lia1]|
          split; [right; reflexivity|]|exact HV2].
        unfold exvu_b.ev_D0. cbn [Z.b2z]. split; [intros _; left; right; split; [exact V0|lia1]|intros _; reflexivity].
Qed.

End EV.
