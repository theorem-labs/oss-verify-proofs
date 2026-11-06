From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct ex_value_c ex_value_m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strtod_c ex_value_c ex_word_c ex_string_c strcmp_c bcmp_c memcpy_c ex_ws_c exvu_b exvu_w.
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

Lemma num_model : forall b i1 jz, X i1 = b :: X (i1 + 1) -> ws b = false ->
  b <> 123 -> b <> 91 -> b <> 34 -> b <> 116 -> b <> 102 -> b <> 110 ->
  (b = 45 /\ jz = 1 \/ b <> 45 /\ jz = 0) ->
  ex_V d (X i1) = match X (i1 + jz) with
    | [] => None
    | c :: z =>
      if negb (digit c) then None
      else if (c =? 48) && match z with c1 :: _ => digit c1 | [] => false end then None
      else let (a, r) := span numch z in
           let txt := firstn (Z.to_nat jz) (X i1) ++ c :: a in
           if whole ex_sm txt then Some (JNum txt (snd (ex_sm txt)), r) else None
    end.
Proof.
  intros b i1 jz XC WSb N1 N2 N3 N4 N5 N6 JZ.
  destruct JZ as [[-> ->]|[Hn ->]].
  - rewrite XC, ex_V_num by assumption. reflexivity.
  - rewrite Z.add_0_r, XC, ex_V_num by assumption. rewrite (proj2 (Z.eqb_neq b 45) Hn). reflexivity.
Qed.

Lemma num_dig : forall c : byte,
  (18446744073709551605 <? (bv_unsigned c + -58) mod 18446744073709551616) = digit (bv_unsigned c).
Proof.
  intros c.
  pose proof (ev_byte_all (fun z => Bool.eqb (18446744073709551605 <? (z + -58) mod 18446744073709551616) (digit z))
    ltac:(vm_compute; reflexivity) c) as H.
  cbv beta in H. apply Bool.eqb_prop in H. exact H.
Qed.

Lemma num_msk : forall c : byte, digit (bv_unsigned c) = false ->
  numch (bv_unsigned c) = ((bv_unsigned c + -43) mod 18446744073709551616 <=? 58) &&
    negb (Z.land (Z.shiftr 288230376218820621 ((bv_unsigned c + -43) mod 64)) 1 =? 0).
Proof.
  intros c Hc.
  pose proof (ev_byte_all (fun z => implb (negb (digit z)) (Bool.eqb (numch z)
    (((z + -43) mod 18446744073709551616 <=? 58) &&
     negb (Z.land (Z.shiftr 288230376218820621 ((z + -43) mod 64)) 1 =? 0))))
    ltac:(vm_compute; reflexivity) c) as H.
  cbv beta in H. rewrite Hc in H. cbn [negb implb] in H. apply Bool.eqb_prop in H. exact H.
Qed.

Lemma num_span : forall a r, Forall (fun z => numch z = true) a ->
  (r = [] \/ exists c r', r = c :: r' /\ numch c = false) -> span numch (a ++ r) = (a, r).
Proof.
  induction a as [|z a IH]; intros r Ha Hr; cbn [app].
  - destruct Hr as [->|(c & r' & -> & Hc)]; [reflexivity|]. cbn [span]. rewrite Hc. reflexivity.
  - apply Forall_cons_iff in Ha as [Hz Ha]. cbn [span]. rewrite Hz, (IH r Ha Hr). reflexivity.
Qed.

Lemma num_split_j : forall b i1 jz, X i1 = b :: X (i1 + 1) -> (jz = 1 \/ jz = 0) ->
  X i1 = firstn (Z.to_nat jz) (X i1) ++ X (i1 + jz).
Proof. intros b i1 jz XC [-> | ->]; [rewrite XC; reflexivity|rewrite Z.add_0_r; reflexivity]. Qed.

Lemma num_numch_rng : forall z, numch z = true -> 43 <= z <= 101.
Proof.
  intros z H. unfold numch, digit in H. repeat rewrite Bool.orb_true_iff in H. rewrite Bool.andb_true_iff in H.
  rewrite ?Z.leb_le, ?Z.eqb_eq in H. lia.
Qed.

Lemma num_bytes_sub : forall m1 a (bs : list byte) k n, bytes_at rsegs m1 a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m1 (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m1 a bs k n H Hkn.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma num_le8 : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  rewrite unsigned_lit_wrap, (Z_to_le_bytes_mod 8 _ 64) by lia.
  rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma num_rw_cons : forall m1 A c cs, rw_cells rsegs m1 A (c :: cs) <->
  rw_cells rsegs m1 A [c] /\ rw_cells rsegs m1 (A + Z.of_nat (csize c)) cs.
Proof.
  intros m1 A c cs. pose proof (ev_rw_app m1 A [c] cs) as H. cbn [app cells_size] in H.
  rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma num_isnumch : forall z, FmtFp_facts3.is_numch z = numch z.
Proof.
  intros z. unfold FmtFp_facts3.is_numch, numch, digit.
  destruct ((48 <=? z) && (z <=? 57)), (z =? 43), (z =? 45), (z =? 46), (z =? 69), (z =? 101); reflexivity.
Qed.

Lemma num_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

Lemma num_memcmp : forall n (l r : list byte), length l = n -> length r = n ->
  exists w, memcmp_model l r n = Some w /\ (w = 0 <-> l = r).
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] Hl Hr; cbn [length] in Hl, Hr; try discriminate.
  - exists 0. split; [reflexivity|tauto].
  - injection Hl as Hl. injection Hr as Hr. cbn [memcmp_model].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r Hl Hr) as (w & H1 & H2). exists w. split; [exact H1|]. rewrite H2.
      split; [intros ->; f_equal; apply bv_eq; exact E|intros H; injection H as _ H; exact H].
    + exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|].
      split; [intros H; exfalso; lia|intros H; injection H as -> _; lia].
Qed.

Lemma num_le8_inj : forall w1 w2 : word, le8 w1 = le8 w2 -> w1 = w2.
Proof. intros w1 w2 H. rewrite <- (le_bytes_to_word_le8 w1), <- (le_bytes_to_word_le8 w2), H. reflexivity. Qed.

Lemma num_fkeep : forall F0 F1 F2 : bvmap 5 word, ex_fkeep F0 F1 ->
  (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F2 k = reg_get F1 k) ->
  ex_fkeep F0 F2.
Proof. intros F0 F1 F2 H1 H2 k Hk. rewrite H2 by (cbn [In] in Hk; lia). apply H1, Hk. Qed.

Lemma num_sm : forall txt bits cn, strtod_model txt = Some (bits, cn) -> ex_sm txt = (cn, bits).
Proof.
  intros txt bits cn H. unfold strtod_model in H.
  change (ex_sm txt) with (match FloatScan.scan_strtod (txt ++ [0]) with Some (b0, c) => (c, b0) | None => (0, 0) end).
  rewrite H. reflexivity.
Qed.

Lemma num_stk_fix : forall m1 m2 l1 h1 a n, stk rsegs m1 l1 h1 -> munch [(a, a + n)] m1 m2 -> wmono rsegs m1 m2 ->
  stk rsegs m2 a (a + n) -> stk rsegs m2 l1 h1.
Proof.
  intros m1 m2 l1 h1 a n (H1 & H2 & H) MU WM (_ & _ & Ha).
  split; [exact H1|]. split; [exact H2|]. intros z Hz.
  destruct (Z_lt_dec z a) as [Hl|Hl]; [|destruct (Z_lt_dec z (a + n)) as [Hh|Hh]].
  2: { apply Ha. lia. }
  all: assert (E : m2 (wa z) = m1 (wa z)) by (apply MU; cbn [outside]; rewrite wa_unsigned by lia; split; [lia|exact I]);
    destruct (H z Hz) as (Hw & b & Hb); split; [apply WM, Hw|]; exists b; unfold mrd in *; rewrite E; exact Hb.
Qed.

Lemma num_stk_rw : forall m1 m2 l1 h1 W A cs, stk rsegs m1 l1 h1 -> munch W m1 m2 -> wmono rsegs m1 m2 ->
  rw_cells rsegs m2 A cs ->
  (forall z, l1 <= z < h1 -> outside W z \/ A <= z < A + Z.of_nat (cells_size cs)) -> stk rsegs m2 l1 h1.
Proof.
  intros m1 m2 l1 h1 W A cs (H1 & H2 & H) MU WM [[Hwf Hb] Hw] Hz.
  split; [exact H1|]. split; [exact H2|]. intros z Hr.
  destruct (Hz z Hr) as [Ho|Hi].
  - assert (E : m2 (wa z) = m1 (wa z)) by (apply MU; rewrite wa_unsigned by lia; exact Ho).
    destruct (H z Hr) as (Hv & b & Hb'). split; [apply WM, Hv|]. exists b. unfold mrd in *. rewrite E. exact Hb'.
  - destruct Hw as (_ & _ & Hw). split.
    + replace z with (A + (z - A)) by lia. apply Hw. lia.
    + destruct Hb as (_ & _ & Hb). rewrite <- (cells_bytes_length cs Hwf) in Hi.
      specialize (Hb (Z.to_nat (z - A)) ltac:(lia)). replace (A + Z.of_nat (Z.to_nat (z - A))) with z in Hb by lia.
      rewrite Hb. destruct (nth_error (cells_bytes cs) (Z.to_nat (z - A))) as [b|] eqn:En; [exists b; reflexivity|].
      apply nth_error_None in En. lia.
Qed.

Lemma num_m43 : forall c : byte, (bv_unsigned c + -43) mod 18446744073709551616 <= 58 ->
  (bv_unsigned c + -43) mod 18446744073709551616 = bv_unsigned c + -43.
Proof. intros c H. pose proof (ev_byte_range c). Z.div_mod_to_equations. lia. Qed.

Lemma num_loop : forall (n : nat) (k : Z) (y1 y5 y6 y7 y8 y9 y11 y15 y16 y17 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28
    y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32) m',
  Z.to_nat (len - k) = n -> 0 <= k < len -> bytes_at rsegs m' x0 x ->
  (forall e a (z15 z16 : word), k <= e <= len -> X k = a ++ X e -> Forall (fun c => numch c = true) a ->
     (e = len \/ exists c r, X e = c :: r /\ numch c = false) ->
     evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (x0 + len)) y11
       (Z_to_bv 64 (-11)) (Z_to_bv 64 58) (Z_to_bv 64 288230376218820621) z15 z16 y17 y18 (Z_to_bv 64 (x0 + e))
       y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x148c4) fc' None m' (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (x0 + len)) y11
    (Z_to_bv 64 (-11)) (Z_to_bv 64 58) (Z_to_bv 64 288230376218820621) y15 y16 y17 y18 (Z_to_bv 64 (x0 + k))
    y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x14898) fc' None m' (seg_rom rsegs)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros k y1 y5 y6 y7 y8 y9 y11 y15 y16 y17 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 F' fc' m'
    Hn Hk BXm K.
  pose proof (ev_read_x m' x0 x k BXm Hk) as RX.
  pose proof (ev_X_cons x k Hk) as XC.
  remember (nth (Z.to_nat k) x (Z_to_bv 8 0)) as c eqn:Ec.
  pose proof (num_dig c) as DG. pose proof (num_msk c) as MK.
  assert (TAIL : numch (bv_unsigned c) = true -> forall z15 z16 : word,
    evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (x0 + len)) y11
      (Z_to_bv 64 (-11)) (Z_to_bv 64 58) (Z_to_bv 64 288230376218820621) z15 z16 y17 y18 (Z_to_bv 64 (x0 + k))
      y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x148b8) fc' None m' (seg_rom rsegs))).
  { intros NC z15 z16. zstep. zstep. if_cases H2.
    - zify_cond H2. replace (x0 + k + 1) with (x0 + (k + 1)) by lia.
      eapply (IHn (n - 1)%nat); [lia|lia|lia|exact BXm|].
      intros e a w15 w16 He Ha Fa Ee. apply (K e (bv_unsigned c :: a) w15 w16); [lia| |constructor; assumption|exact Ee].
      rewrite XC, Ha. reflexivity.
    - zify_cond H2. zstep.
      apply (K len [bv_unsigned c]); [lia| |repeat constructor; exact NC|left; reflexivity].
      assert (Ek : k + 1 = len) by lia.
      rewrite XC, (ev_X_end x (k + 1)) by lia. rewrite (ev_X_end x len) by lia. reflexivity. }
  zstep. zstep. zstep.
  if_cases H1.
  - zify_cond H1. apply TAIL. unfold numch. rewrite <- DG. apply Z.ltb_lt in H1. rewrite H1. reflexivity.
  - zify_cond H1. rewrite (proj2 (Z.ltb_ge _ _) H1) in DG. specialize (MK (eq_sym DG)).
    zstep. zstep. if_cases H2.
    + zify_cond H2. rewrite (proj2 (Z.leb_gt _ _) H2) in MK. cbn [andb] in MK.
      apply (K k []); [lia|reflexivity|constructor|right].
      exists (bv_unsigned c), (X (k + 1)). split; [exact XC|exact MK].
    + zify_cond H2. rewrite (proj2 (Z.leb_le _ _) H2) in MK. cbn [andb] in MK.
      zstep. zstep. zstep. if_cases H3.
      * zify_cond H3. rewrite ?(num_m43 c H2) in H3. rewrite H3 in MK. cbn [negb Z.eqb] in MK.
        apply (K k []); [lia|reflexivity|constructor|right].
        exists (bv_unsigned c), (X (k + 1)). split; [exact XC|exact MK].
      * zify_cond H3. rewrite ?(num_m43 c H2) in H3. rewrite (proj2 (Z.eqb_neq _ _) H3) in MK. cbn [negb] in MK.
        apply TAIL. exact MK.
Qed.

Lemma num_fr_cut5 : forall m1 A w0 w1 w2 w3 w4 cs,
  rw_cells rsegs m1 A (C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: C8 w4 :: cs) <->
  rw_cells rsegs m1 A [C8 w0; C8 w1; C8 w2; C8 w3] /\ rw_cells rsegs m1 (A + 32) [C8 w4] /\
  rw_cells rsegs m1 (A + 40) cs.
Proof.
  intros m1 A w0 w1 w2 w3 w4 cs.
  change (C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: C8 w4 :: cs) with ([C8 w0; C8 w1; C8 w2; C8 w3] ++ C8 w4 :: cs).
  rewrite ev_rw_app.
  change (Z.of_nat (cells_size [C8 w0; C8 w1; C8 w2; C8 w3])) with 32.
  rewrite (num_rw_cons m1 (A + 32) (C8 w4) cs).
  change (Z.of_nat (csize (C8 w4))) with 8.
  replace (A + 32 + 8) with (A + 40) by lia. reflexivity.
Qed.

Lemma num_tag3 : forall t1, tag t1 = 3 -> exists txt bits, t1 = JNum txt bits.
Proof. intros [| | |txt bits| ? | ? | ?] H; cbn in H; try discriminate. exists txt, bits. reflexivity. Qed.

Lemma num_memcmp_rng : forall n (l r : list byte) w, memcmp_model l r n = Some w -> -256 < w < 256.
Proof.
  induction n as [|n IH]; intros l r w H; cbn [memcmp_model] in H.
  - injection H as <-. lia.
  - destruct l as [|a l]; destruct r as [|b r]; try discriminate.
    destruct (bv_unsigned a =? bv_unsigned b); [exact (IH _ _ _ H)|].
    injection H as <-. pose proof (ev_byte_range a). pose proof (ev_byte_range b). lia.
Qed.

Lemma ev_lx63 : forall y, 0 <= y < 2 ^ 63 -> Z.lxor y 9223372036854775808 = y + 9223372036854775808.
Proof. intros y Hy. change 9223372036854775808 with (2 ^ 63). apply zb_lxor_pow2_small; lia. Qed.

Ltac trapz H := zify_cond H; revert H; rewrite ?ev_sgn, ?unsigned_lit by lia1; rewrite ?ev_lx63 by lia1;
  repeat match goal with
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; cbn [Z.b2z]; intro H; rewrite ?Z.lxor_0_l, ?Z.lxor_0_r, ?Z.lxor_nilpotent in H;
  first [lia1 | Z.div_mod_to_equations; lia1 | match type of H with ?T => fail 100 "TRAPFAIL" T end].

Ltac zc H := revert H; rewrite ?unsigned_lit by lia1; intro H; first [lia1 | Z.div_mod_to_equations; lia1].

Lemma ev_num : forall (b : Z) i1 (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) m' j fc' F',
  ev_FI m' j i1 d dl fc' F' -> stk rsegs m' scr (scr + len + 1) -> 0 <= i1 < len ->
  X i1 = b :: X (i1 + 1) -> 0 <= b < 256 -> ws b = false ->
  b <> 123 -> b <> 91 -> b <> 34 -> b <> 116 -> b <> 102 -> b <> 110 ->
  ex_V d (X i0) = ex_V d (X i1) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 v)
    (Z_to_bv 64 (x0 + len)) (Z_to_bv 64 (x0 + i1)) y12 y13 y14 y15 y16 y17 y18 y19 (Z_to_bv 64 b) y21 y22
    y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x14824) fc' None m' (seg_rom rsegs)).
Proof.
  intros b i1 y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 m' j fc' F' HFI SS Hi XC Hb WSb N1 N2 N3 N4 N5 N6 HV.
  assert (LJ : length j = 40%nat) by (destruct HFI as (_ & _ & _ & (((Lj & _) & _) & _) & _); exact Lj).
  destruct (ev_jl_ex j LJ) as (w0 & w8 & w16 & w24 & w32 & ->).
  fi_open HFI.
  pose proof (ev_bx m' MU) as BXm. pose proof ev_vr as VR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (SPU : bv_unsigned (Z_to_bv 64 (SP + -144)) = SP + -144) by (apply unsigned_lit; lia).
  assert (GO : forall i2 jz (u12 : word), (b = 45 /\ jz = 1 \/ b <> 45 /\ jz = 0) -> i2 = i1 + jz ->
    evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 v)
      (Z_to_bv 64 (x0 + len)) (Z_to_bv 64 (x0 + i1)) u12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 (x0 + i2)) (Z_to_bv 64 b)
      y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x1483c) fc' None m' (seg_rom rsegs))).
  2:{ zstep. zstep. zstep. if_cases HJ; zify_cond HJ.
      - apply (GO i1 0); [right; split; [zc HJ|reflexivity]|lia1].
      - zstep. zstep. if_cases HT; [exfalso; trapx HT|]. zstep.
        replace (x0 + i1 + 1) with (x0 + (i1 + 1)) by lia1.
        apply (GO (i1 + 1) 1); [left; split; [zc HJ|reflexivity]|reflexivity]. }
  intros i2 jz u12 JZ Ei2.
  assert (JZr : 0 <= jz <= 1) by (destruct JZ; lia).
  rewrite (num_model b i1 jz XC WSb N1 N2 N3 N4 N5 N6 JZ) in HV.
  rewrite <- Ei2 in HV.
  zstep. zstep.
  if_cases H1.
  { zify_cond H1. rewrite (ev_X_end x i2) in HV by lia.
    eapply ev_epi; [exact HFI|]. unfold exvu_b.ev_FIN. rewrite HV. split; [reflexivity|lia]. }
  zify_cond H1.
  assert (Hi2 : 0 <= i2 < len) by lia.
  pose proof (ev_read_x m' x0 x i2 BXm Hi2) as RX.
  pose proof (ev_X_cons x i2 Hi2) as XC2.
  remember (nth (Z.to_nat i2) x (Z_to_bv 8 0)) as c eqn:Ec.
  pose proof (num_dig c) as DG.
  rewrite XC2 in HV. cbv beta iota in HV.
  zstep. zstep. zstep. zstep.
  if_cases H2.
  { zify_cond H2. assert (DGc : digit (bv_unsigned c) = false) by (rewrite <- DG; apply Z.ltb_ge; lia).
    rewrite DGc in HV. cbn [negb] in HV.
    eapply ev_epi; [exact HFI|]. unfold exvu_b.ev_FIN. rewrite HV. split; [reflexivity|lia]. }
  zify_cond H2. assert (DGc : digit (bv_unsigned c) = true) by (rewrite <- DG; apply Z.ltb_lt; lia).
  rewrite DGc in HV. cbn [negb] in HV.
  assert (REST : (bv_unsigned c =? 48) && match X (i2 + 1) with c1 :: _ => digit c1 | [] => false end = false ->
    forall w12 w13 w14 : word, evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q)
      (Z_to_bv 64 v) (Z_to_bv 64 (x0 + len)) (Z_to_bv 64 (x0 + i1)) w12 w13 w14 y15 y16 y17 (Z_to_bv 64 (-1))
      (Z_to_bv 64 (x0 + i2)) (Z_to_bv 64 b) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x1487c) fc'
      None m' (seg_rom rsegs))).
  { intros NZ w12 w13 w14.
    rewrite NZ in HV. cbn [andb] in HV.
    do 7 zstep.
    eapply (num_loop (Z.to_nat (len - i2)) i2); [reflexivity|lia|exact BXm|].
    intros e a z15 z16 He Ha Fa Ee.
    assert (NCc : numch (bv_unsigned c) = true) by (unfold numch; rewrite DGc; reflexivity).
    destruct a as [|c0 a'].
    { exfalso. cbn [app] in Ha. destruct Ee as [Ee|(c2 & r2 & Ee & Nc2)].
      - subst e. rewrite (ev_X_end x len) in Ha by lia. rewrite XC2 in Ha. discriminate.
      - rewrite <- Ha, XC2 in Ee. injection Ee as <- _. congruence. }
    rewrite XC2 in Ha. cbn [app] in Ha. injection Ha as Ec0 Xa'. subst c0.
    apply Forall_cons_iff in Fa as [_ Fa'].
    assert (EX : X e = [] \/ exists c2 r2, X e = c2 :: r2 /\ numch c2 = false).
    { destruct Ee as [->|Ee]; [left; apply ev_X_end; lia|right; exact Ee]. }
    rewrite Xa', (num_span a' (X e) Fa' EX) in HV. cbv beta iota zeta in HV.
    remember (firstn (Z.to_nat jz) (X i1) ++ bv_unsigned c :: a') as txt eqn:Etxt.
    assert (TX : X i1 = txt ++ X e).
    { rewrite Etxt, <- app_assoc. cbn [app]. rewrite <- Xa', <- XC2, Ei2.
      apply (num_split_j b i1 jz XC). destruct JZ as [[_ ?]|[_ ?]]; auto. }
    assert (LT : Z.of_nat (length txt) = e - i1 /\ i2 < e).
    { pose proof (f_equal (@length Z) TX) as L. rewrite length_app in L.
      pose proof (f_equal (@length Z) Xa') as L3. rewrite length_app in L3.
      pose proof (ev_X_len x i1 ltac:(lia)) as L1. pose proof (ev_X_len x e ltac:(lia)) as L2.
      pose proof (ev_X_len x (i2 + 1) ltac:(lia)) as L4. lia. }
    destruct LT as [LT He2].
    assert (FB : Forall (fun z => 0 <= z < 256) txt).
    { pose proof (ev_bytes_X x i1) as B. rewrite TX in B. apply Forall_app in B. exact (proj1 B). }
    assert (FN : Forall (fun z => numch z = true) txt).
    { rewrite Etxt. apply Forall_app. split; [|constructor; assumption].
      destruct JZ as [[Hb1 ->]|[_ ->]]; [|constructor].
      rewrite XC, Hb1. change (Z.to_nat 1) with 1%nat. cbn [firstn]. repeat constructor. }
    assert (FP : Forall (fun z => 0 < z < 256) txt).
    { eapply Forall_impl; [|exact FN]. intros z Hz. pose proof (num_numch_rng z Hz). lia. }
    assert (MB : map (Z_to_bv 8) txt = firstn (Z.to_nat (e - i1)) (skipn (Z.to_nat i1) x)).
    { rewrite <- (ev_map_Xb x i1), TX, map_app. rewrite <- LT, Nat2Z.id.
      rewrite <- (length_map (Z_to_bv 8) txt). symmetry. apply firstn_app_exact. }
    pose proof (stk_split rsegs m' scr (scr + (e - i1)) (scr + len + 1) SS ltac:(lia)) as [SS1 SS2].
    pose proof (stk_split rsegs m' (scr + (e - i1)) (scr + (e - i1) + 1) (scr + len + 1) SS2 ltac:(lia)) as [SSb SS3].
    clear SS SS2.
    destruct (stk_carve rsegs m' scr (scr + (e - i1)) (Z.to_nat (e - i1)) SS1 ltac:(lia)) as [_ [junk JK]].
    replace (scr + (e - i1) - Z.of_nat (Z.to_nat (e - i1))) with scr in JK by lia.
    clear SS1.
    zstep. zstep.
    replace (Z_to_bv 64 (x0 + e - (x0 + i1))) with (Z_to_bv 64 (e - i1)) by (f_equal; lia1).
    zstep.
    eapply evt_cut.
    { eapply MCC with (src := map (Z_to_bv 8) txt) (junk := junk).
      - rewrite unsigned_lit by lia1. rewrite MB. replace (x0 + i1) with (x0 + Z.of_nat (Z.to_nat i1)) by lia1.
        apply num_bytes_sub; [exact BXm|lia1].
      - rewrite length_map, unsigned_lit by lia1. lia1.
      - rewrite !unsigned_lit by lia1. exact JK.
      - rewrite !unsigned_lit by lia1. ap AXS. lia1.
      - exact MI. }
    intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E &
      MUc & WMc & MIc & RWc & BSc).
    subst ms'. rewrite !unsigned_lit in MUc by lia1. rewrite !unsigned_lit in RWc by lia1.
    replace (ret_pc (Z_to_bv 64 0x148d0)) with (Z_to_bv 64 0x148d0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear BSc.
    assert (STk : True /\ stk rsegs m' lo (SP + -144)) by (split; [exact I|exact ST]). clear ST.
    ap AXS. ap AQS.
    transport_after_call rsegs m' m2 MUc WMc. clear A A0.
    assert (SSa : stk rsegs m2 scr (scr + (e - i1))).
    { pose proof (stk_of_rw_cells rsegs m2 scr _ RWc) as H. cbn [cells_size csize] in H.
      replace (scr + (e - i1)) with (scr + Z.of_nat (Z.to_nat (e - i1) + 0)) by lia1. exact H. }
    destruct STk as [_ ST]. pose proof (num_stk_fix m' m2 lo (SP + -144) scr (e - i1) ST MUc WMc SSa) as ST'.
    clear ST MUc WMc. rename ST' into ST.
    zstep. zstep. zstep. zstep.
    pose proof (ev_stk_wr m2 (scr + (e - i1)) (scr + (e - i1) + 1) SSb ltac:(lia1)) as WZ.
    replace (scr + (e - i1) + 1 - (scr + (e - i1))) with 1 in WZ by lia1.
    pose proof (wr_at_store_ok rsegs m2 (scr + (e - i1)) 1 0 1%nat WZ ltac:(lia1) ltac:(lia1)) as HS.
    rewrite Z.add_0_r in HS.
    clear WZ.
    zstep. zstep. zstep. if_cases HT1; [exfalso; trapz HT1|].
    zstep. zstep. zstep. zstep. zstep. if_cases HT2; [exfalso; trapz HT2|].
    zstep. if_cases HT3; [exfalso; trapz HT3|].
    zstep.
    pose proof (bytes_at_write_same rsegs m2 (scr + (e - i1)) (le1 (Z_to_bv 64 0)) ltac:(lia1)
      ltac:(rewrite length_le1; lia1)) as BZ.
    ap AXS. ap AQS.
    store_done. clear A A0.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in BZ.
    assert (BT : bytes_at rsegs m3 scr (map (Z_to_bv 8) (txt ++ [0]))).
    { rewrite map_app. apply bytes_at_app. split.
      - pose proof RWc as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
      - rewrite length_map, LT. exact BZ. }
    assert (LBT : Z.of_nat (length (map (Z_to_bv 8) (txt ++ [0]))) = e - i1 + 1).
    { rewrite length_map, length_app. cbn [length]. lia1. }
    clear BZ.
    apply (proj1 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
    apply num_fr_cut5 in FR as (FRa & FRe & FRs).
    replace (SP + -144 + 32) with (SP + -112) in FRe by lia1.
    pose proof (stk_split rsegs m3 lo (SP + -144 - 8928) (SP + -144) ST ltac:(lia1)) as [STa STb]. clear ST.
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply SDC with (s := scr) (e := SP + -112) (txt := txt).
      - reflexivity.
      - f_equal; lia1.
      - exact HTP.
      - exact BT.
      - eapply Forall_impl; [|exact FN]. intros z Hz. rewrite num_isnumch. exact Hz.
      - lia1.
      - exact FRe.
      - rewrite SPU. exact STb.
      - rewrite SPU. unfold STRTOD_GLOBALS_TOP, STRTOD_K. lia1.
      - rewrite SPU. lia1.
      - exact SG.
      - lia1.
      - rewrite SPU. unfold STRTOD_IMG_LO, STRTOD_GLOBALS_TOP, STRTOD_K. left. split; lia1.
      - rewrite SPU. right. lia1.
      - lia1.
      - right. lia1.
      - exact (ev_gg m3 MU WM).
      - exact (ev_gq m3 MU WM).
      - exact EV.
      - assumption.
      - exact (ev_tm m3 MU).
      - exact FRM. }
    intros ms' PO.
    destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5''
      & t6'' & F4 & fc4 & m4 & ev4 & cn & bits & E4 & SM & Hcn & RE4 & FA4 & FO4 & FRM4 & EV4 & MU4 & WM4 & MI4 & TM4
      & ST4).
    subst ms'. rewrite SPU in MU4. rewrite SPU in ST4.
    unfold STRTOD_K in MU4, ST4. unfold STRTOD_ERRNO in MU4, EV4.
    replace (ret_pc (Z_to_bv 64 0x14914)) with (Z_to_bv 64 0x14914) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    ap AXW. ap AXE. ap AQW.
    assert (STk : True /\ stk rsegs m3 lo (SP + -144 - 8928)) by (split; [exact I|exact STa]). clear STa.
    assert (STa : stk rsegs m4 lo (SP + -144 - 8928)).
    { apply (num_stk_rw m3 m4 lo (SP + -144 - 8928) _ 217764 [C4 ev4] (proj2 STk) MU4 WM4 EV4).
      intros z Hz. cbn [cells_size csize]. destruct (Z_lt_dec z 217764) as [Hl|Hl];
        [|destruct (Z_lt_dec z (217764 + 4)) as [Hh|Hh]]; [left|right; lia|left]; cbn [outside]; repeat split; lia. }
    clear STk.
    transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4 A A0 A1.
    replace (SP + -112) with (SP + -144 + 32) in RE4 by lia1.
    pose proof (proj2 (num_fr_cut5 _ _ _ _ _ _ _ _) (conj FRa (conj RE4 FRs))) as FR. clear FRa RE4 FRs.
    pose proof (stk_merge rsegs m4 lo (SP + -144 - 8928) (SP + -144) STa ST4 ltac:(lia1)) as ST. clear STa ST4.
    pose proof (num_fkeep F F' F4 FK FO4) as FK4.
    pose proof (num_sm txt bits cn SM) as ESM.
    pose proof (ex_sm_range txt) as BR. rewrite ESM in BR. cbn [snd] in BR.
    unfold whole in HV. rewrite ESM in HV. cbn [fst snd] in HV.
    assert (Hcn' : 0 <= cn < Z.of_nat (length (map (Z_to_bv 8) (txt ++ [0])))) by lia1.
    assert (FA4' : forall k : bv 5, bv_unsigned k = 10 -> reg_get F4 k = Z_to_bv 64 bits).
    { intros k Hk. rewrite <- FA4. f_equal. apply bv_eq. rewrite Hk. reflexivity. }
    ap AQW. ap AXW. ap AQX.
    zstep. zstep.
    repeat match goal with
    | |- context [reg_get F4 ?k] => rewrite (FA4' k ltac:(vm_compute; reflexivity))
    | H : context [reg_get F4 ?k] |- _ =>
        lazymatch H with FA4 => fail | FA4' => fail | FO4 => fail | _ =>
          rewrite (FA4' k ltac:(vm_compute; reflexivity)) in H end
    end.
    pose proof (ev_read_x _ scr _ cn BT Hcn') as RB. rewrite map_nth in RB.
    set (bz := nth (Z.to_nat cn) (txt ++ [0]) 0) in *.
    assert (BZ : cn = Z.of_nat (length txt) /\ bz = 0 \/ cn < Z.of_nat (length txt) /\ 0 < bz < 256).
    { destruct (Z.eq_dec cn (Z.of_nat (length txt))) as [E|E].
      - left. split; [exact E|]. unfold bz. rewrite E, Nat2Z.id, app_nth2, Nat.sub_diag by lia. reflexivity.
      - right. split; [lia|]. unfold bz. rewrite app_nth1 by lia. rewrite Forall_forall in FP. apply FP.
        apply nth_In. lia. }
    assert (Ebz : bv_unsigned (Z_to_bv 8 bz) = bz) by (apply num_u8; destruct BZ; lia).
    clearbody bz.
    zstep. if_cases HTe; [exfalso; trapx HTe|].
    zstep. cbv beta. rewrite Ebz.
    zstep. if_cases H3.
    { zify_cond H3.
      assert (CN : cn < Z.of_nat (length txt)) by (destruct BZ as [[? ?]|[? ?]]; lia1).
      rewrite (proj2 (Z.eqb_neq _ _)) in HV by lia1. cbn [andb] in HV.
      apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
      eapply ev_epi; [fi_pack|]. unfold exvu_b.ev_FIN. rewrite HV. split; [reflexivity|]. lia1. }
    zify_cond H3.
    assert (CN : cn = Z.of_nat (length txt)) by (destruct BZ as [[? ?]|[? ?]]; lia1).
    rewrite (proj2 (Z.eqb_eq _ _) CN) in HV. cbn [andb] in HV.
    pose proof (ex_class bits) as EC. rewrite Z.mod_small in EC by lia1.
    zstep. zstep. zstep. zstep.
    if_cases H4; zify_cond H4; cbv beta iota zeta delta [fread fget c_fregs] in H4; cbn [fp_format] in H4;
      change 18446744073709551616 with (2 ^ 64) in H4; rewrite <- land_mask_mod in H4 by lia1;
      repeat match type of H4 with context [reg_get F4 ?k] => rewrite (FA4' k ltac:(vm_compute; reflexivity)) in H4 end;
      rewrite ?unsigned_lit in H4 by lia1; try rewrite FA4 in H4; rewrite ?unsigned_lit in H4 by lia1.
    { assert (NF : finite bits = false) by (destruct (finite bits) eqn:Ef; [|reflexivity]; exfalso; pose proof (proj2 EC eq_refl); lia1).
      rewrite NF in HV.
      apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
      eapply ev_epi; [fi_pack|]. unfold exvu_b.ev_FIN. rewrite HV. split; [reflexivity|]. lia1. }
    assert (FT : finite bits = true).
    { apply EC. match type of H4 with ?L <= 0 => assert (0 <= L) by (apply Z.land_nonneg; right; lia1) end. lia1. }
    rewrite FT in HV.
    ev_stash. ap AQW. ap AQX.
    pose proof (stk_merge rsegs _ _ _ _ SSa SSb ltac:(lia1)) as S1.
    pose proof (stk_merge rsegs _ _ _ _ S1 SS3 ltac:(lia1)) as S2. clear S1.
    assert (DL1 : 1 = 0 \/ 1 = 1) by (right; reflexivity).
    assert (PV : e = len - Z.of_nat (length (X e))) by (rewrite ev_X_len by lia1; lia1).
    zstep. if_cases Hv0; zify_cond Hv0.
    { assert (Hv : v = 0) by (revert Hv0; rewrite ?unsigned_lit by lia1; lia1).
      zstep. zstep. zstep.
      apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
      eapply ev_epi with (pv := e) (dep := d) (dl' := dl); [ev_fipack|].
      unfold exvu_b.ev_FIN. rewrite HV. cbv beta iota. split; [reflexivity|]. split; [exact PV|]. split; [reflexivity|].
      split; [exact S2|]. split; [intros H; left; exact H|intros [H|[H _]]; [exact H|exfalso; exact (H Hv)]]. }
    assert (Hv : v <> 0) by (revert Hv0; rewrite ?unsigned_lit by lia1; lia1).
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (ev_tree mm Hv MU) as TN end.
    destruct (ev_hdr _ _ _ _ _ TN) as (num & str & kids & keys & nn & cap & HH).
    pose proof (ev_u32_rd _ _ _ (proj1 (proj2 HH))) as RT.
    pose proof (ev_tag_range t) as TR.
    destruct HH as ((_ & (P1 & P2 & _)) & _).
    pose proof (ev_al8 v (ev_v8 Hv)) as HL.
    zstep. zstep. if_cases HTv; [exfalso; trapx HTv|].
    zstep. rewrite ?ev_sx32 by lia1.
    zstep. zstep. if_cases Ht; zify_cond Ht.
    { assert (Ht3 : tag t <> 3) by (revert Ht; rewrite ?unsigned_lit by lia1; lia1).
      zstep. zstep. zstep. zstep. zstep.
      apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
      eapply ev_epi with (pv := e) (dep := d) (dl' := 1); [ev_fipack|].
      unfold exvu_b.ev_FIN. rewrite HV. cbv beta iota. split; [reflexivity|]. split; [exact PV|]. split; [reflexivity|].
      split; [exact S2|].
      split; [intros _; right; split; [exact Hv|intros E; rewrite E in Ht3; exact (Ht3 eq_refl)]|intros _; reflexivity]. }
    assert (Ht3 : tag t = 3) by (revert Ht; rewrite ?unsigned_lit by lia1; lia1).
    destruct (num_tag3 t Ht3) as (txt' & bits' & Et).
    pose proof TN as TN'. rewrite Et in TN'. cbn [pj_node] in TN'.
    destruct TN' as (_ & _ & num' & str' & kids' & keys' & n' & cap' & HH' &
      (Enum & _ & _ & _ & _ & k & (_ & _ & Fs & Bs) & _)).
    destruct HH' as (_ & _ & U8 & U16 & _). destruct U8 as [U8r U8b].
    pose proof (ev_u64_rd _ _ _ U16) as RSTR. destruct U16 as [SR _].
    rewrite map_app in Bs.
    pose proof BT as BT'. rewrite map_app in BT'. cbn [map] in BT'.
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply SCC with (sx := map (Z_to_bv 8) txt') (sy := map (Z_to_bv 8) txt).
      - rewrite unsigned_lit by lia1. exact Bs.
      - exact (ev_no0 txt' Fs).
      - rewrite unsigned_lit by lia1. exact BT'.
      - exact (ev_no0 txt FP). }
    intros ms' PO. destruct PO as (r2 & z11 & z12 & z13 & E2 & Hr). subst ms'.
    replace (ret_pc (Z_to_bv 64 0x1495c)) with (Z_to_bv 64 0x1495c) by (symmetry; apply ret_pc_even; [lia1|reflexivity]).
    zstep. if_cases Hc0; zify_cond Hc0.
    { assert (Es : map (Z_to_bv 8) txt' <> map (Z_to_bv 8) txt).
      { intros Es. apply Hc0. rewrite (proj2 Hr Es). reflexivity. }
      zstep. zstep. zstep. zstep. zstep.
      apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
      eapply ev_epi with (pv := e) (dep := d) (dl' := 1); [ev_fipack|].
      unfold exvu_b.ev_FIN. rewrite HV. cbv beta iota. split; [reflexivity|]. split; [exact PV|]. split; [reflexivity|].
      split; [exact S2|].
      split; [intros _; right; split; [exact Hv|rewrite Et; intros E; apply Es; congruence]|intros _; reflexivity]. }
    assert (R0 : r2 = Z_to_bv 64 0) by (apply bv_eq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia1).
    assert (Es : txt' = txt).
    { apply ev_map_inj; [eapply Forall_impl; [|exact Fs]; intros a [? ?]; lia1
                        |eapply Forall_impl; [|exact FP]; intros a [? ?]; lia1
                        |apply Hr; exact R0]. }
    subst txt'.
    pose proof (proj2 (proj1 (num_rw_cons _ _ _ _) FR)) as FRt1.
    pose proof (proj2 (proj1 (num_rw_cons _ _ _ _) FRt1)) as FRt2.
    pose proof (proj2 (proj1 (num_rw_cons _ _ _ _) FRt2)) as FRt3.
    pose proof (proj1 (proj1 (num_rw_cons _ _ _ _) FRt3)) as FRb.
    pose proof (ev_rw8_bytes _ _ _ FRb) as BB. clear FRt1 FRt2 FRt3 FRb.
    match type of BB with bytes_at _ _ ?A _ => replace A with (SP + -120) in BB by (cbn [csize]; lia1) end.
    destruct (num_memcmp 8 (le8 (Z_to_bv 64 num')) (le8 (Z_to_bv 64 bits)) ltac:(apply length_le8)
      ltac:(apply length_le8)) as (w & MW & Hw).
    pose proof (num_memcmp_rng _ _ _ _ MW) as WR.
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply BCC with (ls := le8 (Z_to_bv 64 num')) (rs := le8 (Z_to_bv 64 bits)) (v := w).
      - rewrite unsigned_lit by lia1. exact U8b.
      - rewrite unsigned_lit by lia1. match goal with |- bytes_at _ _ ?A _ => replace A with (SP + -120) by lia1 end.
        exact BB.
      - change (Z.to_nat (bv_unsigned (Z_to_bv 64 8))) with 8%nat. exact MW.
      - exact MI4. }
    intros ms' PO.
    destruct PO as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m5 & E5 & MU5 &
      WM5 & MI5 & B5a & B5b).
    subst ms'. clear B5a B5b.
    replace (ret_pc (Z_to_bv 64 0x14970)) with (Z_to_bv 64 0x14970) by (symmetry; apply ret_pc_even; [lia1|reflexivity]).
    match type of MU5 with munch _ ?mm _ => transport_after_call rsegs mm m5 MU5 WM5 end. clear MU5 WM5.
    zstep. if_cases Hw0; zify_cond Hw0.
    { assert (W0 : w = 0) by (revert Hw0; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia).
      assert (EB : Z_to_bv 64 num' = Z_to_bv 64 bits) by (apply num_le8_inj; apply Hw; exact W0).
      apply (f_equal (@bv_unsigned 64)) in EB. rewrite !unsigned_lit in EB by lia1.
      zstep. zstep. zstep.
      apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
      eapply ev_epi with (pv := e) (dep := d) (dl' := dl); [ev_fipack|].
      unfold exvu_b.ev_FIN. rewrite HV. cbv beta iota. split; [reflexivity|]. split; [exact PV|]. split; [reflexivity|].
      split; [exact S2|].
      split; [intros H; left; exact H|intros [H|[_ H]]; [exact H|exfalso; apply H; rewrite Et; congruence]]. }
    assert (WN : w <> 0) by (revert Hw0; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia).
    assert (EB : num' <> bits) by (intros E; apply WN; apply Hw; rewrite E; reflexivity).
    zstep. zstep. zstep. zstep. zstep.
    apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
    eapply ev_epi with (pv := e) (dep := d) (dl' := 1); [ev_fipack|].
    unfold exvu_b.ev_FIN. rewrite HV. cbv beta iota. split; [reflexivity|]. split; [exact PV|]. split; [reflexivity|].
    split; [exact S2|].
    split; [intros _; right; split; [exact Hv|rewrite Et; intros E; apply EB; congruence]|intros _; reflexivity]. }
  zstep. zstep. if_cases H3.
  { zify_cond H3. apply REST. rewrite (proj2 (Z.eqb_neq (bv_unsigned c) 48) H3). reflexivity. }
  zify_cond H3. zstep. zstep. if_cases HTz; [exfalso; trapx HTz|]. zstep. zstep. if_cases H4.
  { zify_cond H4. apply REST. rewrite (ev_X_end x (i2 + 1)) by lia. destruct (bv_unsigned c =? 48); reflexivity. }
  zify_cond H4.
  pose proof (ev_read_x m' x0 x (i2 + 1) BXm ltac:(lia)) as RX1.
  replace (x0 + (i2 + 1)) with (x0 + i2 + 1) in RX1 by lia.
  pose proof (ev_X_cons x (i2 + 1) ltac:(lia)) as XC3.
  remember (nth (Z.to_nat (i2 + 1)) x (Z_to_bv 8 0)) as c1 eqn:Ec1.
  pose proof (num_dig c1) as DG1.
  zstep. zstep. zstep. zstep. if_cases H5.
  { zify_cond H5. assert (DGc1 : digit (bv_unsigned c1) = true) by (rewrite <- DG1; apply Z.ltb_lt; lia).
    rewrite H3, Z.eqb_refl, XC3 in HV. cbn [andb] in HV. rewrite DGc1 in HV. cbn [andb] in HV.
    zstep. zstep.
    eapply ev_epi; [exact HFI|]. unfold exvu_b.ev_FIN. rewrite HV. split; [reflexivity|lia]. }
  zify_cond H5. assert (DGc1 : digit (bv_unsigned c1) = false) by (rewrite <- DG1; apply Z.ltb_ge; lia).
  apply REST. rewrite XC3. destruct (bv_unsigned c =? 48); cbn [andb]; [exact DGc1|reflexivity].
Qed.

End EV.
