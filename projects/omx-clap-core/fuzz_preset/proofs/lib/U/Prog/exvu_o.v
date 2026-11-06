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

Lemma objn_colon : forall i i3 (n : nat) vv dlB kid fl sv (w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 : word) m4 j fc' F',
  ev_FI m4 j i3 (d + 1) dlB fc' F' -> stk rsegs m4 scr (scr + len + 1) -> 0 <= i3 <= len ->
  ex_name true (X i) = match X i3 with c0 :: r1 => if c0 =? 58 then Some (sv, r1) else None | [] => None end ->
  (ex_name true (X i) = None -> ex_V d (X i0) = None) ->
  (i3 < len -> ex_name true (X i) = Some (sv, X (i3 + 1)) ->
   forall m'' (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word),
     ev_FI m'' j (i3 + 1) (d + 1) dlB fc' F' -> stk rsegs m'' scr (scr + len + 1) ->
     evt rsegs ev_Q (MS (mkR z1 (Z_to_bv 64 (SP + -144)) gp tp z5 z6 z7 (Z_to_bv 64 q) (Z_to_bv 64 vv) z10 z11 z12
      z13 z14 z15 z16 z17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 123) (Z_to_bv 64 44)
      (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123)
      (Z_to_bv 64 (-1)) (Z_to_bv 64 fl) z28 z29 z30 z31) F' (Z_to_bv 64 0x14bd0) fc' None m'' (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR w1 (Z_to_bv 64 (SP + -144)) gp tp w5 w6 w7 (Z_to_bv 64 q) (Z_to_bv 64 vv) w10 w11 w12
      w13 w14 w15 w16 w17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 123) (Z_to_bv 64 44)
      (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123)
      (Z_to_bv 64 (-1)) (Z_to_bv 64 fl) w28 w29 w30 w31) F' (Z_to_bv 64 0x14ba8) fc' None m4 (seg_rom rsegs)).
Proof.
  intros i i3 n vv dlB kid fl sv w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m4 j fc' F' HFI SS Hi EN HN K.
  fi_open HFI. ap AQW. ap AQX. ap AQS.
  pose proof (ev_bx m4 MU) as BXm.
  zstep. zstep. zstep. if_cases H1.
  - zify_cond H1. eapply ev_epi; [exact HFI|]. unfold exvu_b.ev_FIN. rewrite HN; [split; [reflexivity|lia]|].
    rewrite EN, (ev_X_end x i3) by lia. reflexivity.
  - zify_cond H1.
    zstep. if_cases HT; [exfalso; trapx HT|].
    pose proof (ev_read_x m4 x0 x i3 BXm ltac:(lia)) as RX.
    pose proof (ev_X_cons x i3 ltac:(lia)) as XC.
    remember (nth (Z.to_nat i3) x (Z_to_bv 8 0)) as b eqn:Eb.
    pose proof (ev_byte_range b) as Rb.
    rewrite XC in EN. cbv beta iota in EN.
    zstep. zstep. zstep. if_cases H2.
    + zify_cond H2. eapply ev_epi; [exact HFI|]. unfold exvu_b.ev_FIN. rewrite HN; [split; [reflexivity|lia]|].
      rewrite EN, (proj2 (Z.eqb_neq _ _) H2). reflexivity.
    + zify_cond H2. rewrite H2 in EN.
      zstep. if_cases HT2; [exfalso; trapx HT2|].
      zstep. zstep.
      replace (x0 + i3 + 1) with (x0 + (i3 + 1)) in * by lia.
      eapply (K ltac:(lia) EN); [fi_pack|exact SS].
Qed.

Lemma objn_after : forall i i2 (n : nat) vv dlB kid fl sv (w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 : word) m3 j fc' F',
  ev_FI m3 j i2 (d + 1) dlB fc' F' -> stk rsegs m3 scr (scr + len + 1) -> 0 <= i2 <= len ->
  ex_name true (X i) = match skip (X i2) with c0 :: r1 => if c0 =? 58 then Some (sv, r1) else None | [] => None end ->
  (ex_name true (X i) = None -> ex_V d (X i0) = None) ->
  (forall i3, i2 <= i3 < len -> ex_name true (X i) = Some (sv, X (i3 + 1)) ->
   forall m'' (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word),
     ev_FI m'' j (i3 + 1) (d + 1) dlB fc' F' -> stk rsegs m'' scr (scr + len + 1) ->
     evt rsegs ev_Q (MS (mkR z1 (Z_to_bv 64 (SP + -144)) gp tp z5 z6 z7 (Z_to_bv 64 q) (Z_to_bv 64 vv) z10 z11 z12
      z13 z14 z15 z16 z17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 123) (Z_to_bv 64 44)
      (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123)
      (Z_to_bv 64 (-1)) (Z_to_bv 64 fl) z28 z29 z30 z31) F' (Z_to_bv 64 0x14bd0) fc' None m'' (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR w1 (Z_to_bv 64 (SP + -144)) gp tp w5 w6 w7 (Z_to_bv 64 q) (Z_to_bv 64 vv) w10 w11 w12
      w13 w14 w15 w16 w17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 123) (Z_to_bv 64 44)
      (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123)
      (Z_to_bv 64 (-1)) (Z_to_bv 64 fl) w28 w29 w30 w31) F' (Z_to_bv 64 0x14ba0) fc' None m3 (seg_rom rsegs)).
Proof.
  intros i i2 n vv dlB kid fl sv w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m3 j fc' F' HFI SS Hi EN HN K.
  zstep. zstep.
  eapply (ev_ws i2 0x14ba8); [lia|reflexivity|lia|exact HFI|].
  intros i3 m4 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 FI4 Hr HX MU4 WM4.
  eapply (objn_colon i i3 n vv dlB kid fl sv); [exact FI4| |lia| |exact HN|].
  + eapply stk_transport_disjoint; [exact SS|exact MU4|exact WM4|cbn [disjoint_from]; split; [ap AQS; lia|exact I]].
  + rewrite EN, <- HX. reflexivity.
  + intros Hl. exact (K i3 ltac:(lia)).
Qed.

Lemma objn_key : forall i2 (n : nat) vv dlA kid fl sv (w0 w24 w32 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 : word) m3 fc' F',
  ev_FI m3 (ev_jl w0 (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 125) w24 w32) i2 (d + 1) dlA fc' F' -> stk rsegs m3 scr (scr + len + 1) ->
  bytes_at rsegs m3 scr (map (Z_to_bv 8) sv ++ [Z_to_bv 8 0]) -> Forall (fun c => 0 < c < 256) sv ->
  ev_VV true vv -> ev_KID vv n kid fl -> (dlA = 0 \/ dlA = 1) -> Z.of_nat n <= len ->
  (forall m4 dlB (u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word),
     ev_FI m4 (ev_jl w0 (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 125) w24 w32) i2 (d + 1) dlB fc' F' -> stk rsegs m4 scr (scr + len + 1) -> (dlB = 0 \/ dlB = 1) ->
     (dlB = 1 <-> dlA = 1 \/ (fl = 1 /\ fst (nth n (tkids t) ([], JNull)) <> sv)) ->
     evt rsegs ev_Q (MS (mkR u1 (Z_to_bv 64 (SP + -144)) gp tp u5 u6 u7 (Z_to_bv 64 q) (Z_to_bv 64 vv) u10 u11 u12
      u13 u14 u15 u16 u17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 123) (Z_to_bv 64 44)
      (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123)
      (Z_to_bv 64 (-1)) (Z_to_bv 64 fl) u28 u29 u30 u31) F' (Z_to_bv 64 0x14ba0) fc' None m4 (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR w1 (Z_to_bv 64 (SP + -144)) gp tp w5 w6 w7 (Z_to_bv 64 q) (Z_to_bv 64 vv) w10 w11 w12
      w13 w14 w15 w16 w17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 123) (Z_to_bv 64 44)
      (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123)
      (Z_to_bv 64 (-1)) (Z_to_bv 64 fl) w28 w29 w30 w31) F' (Z_to_bv 64 0x14b48) fc' None m3 (seg_rom rsegs)).
Proof.
  intros i2 n vv dlA kid fl sv w0 w24 w32 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m3 fc' F' HFI SS BS FS VV KID DLA Hnl K.
  destruct KID as [(-> & -> & _)|(-> & -> & Hv & Hn & _)].
  - zstep. first [if_true | if_false | idtac].
    apply (K m3 dlA); [exact HFI|exact SS|exact DLA|].
    split; [left; assumption|]. intros [?|[? _]]; [assumption|lia].
  - destruct VV as [(E0 & _)|(_ & _ & Htag)]; [lia|].
    fi_open HFI. pose proof ev_vr as VR. ap AQW. ap AQS.
    pose proof (ev_tree m3 Hv MU) as TR.
    destruct (ev_node_cont _ _ _ _ _ true TR Htag) as (num & kids & keys & cap & HH & HC).
    destruct (HC n Hn) as (Hcap & _ & _ & HK).
    destruct (HK eq_refl) as (HinY & xk & k & UK & CK & _).
    destruct (ev_D8 Hv _ _ HinY) as (KYp & KY8).
    destruct HH as (_ & _ & _ & _ & _ & P32 & P40 & _).
    pose proof (ev_u64_rd _ _ _ P32) as RK1. pose proof (ev_u64_rd _ _ _ UK) as RK2.
    pose proof (bytes_at_bound rsegs _ _ _ (proj2 UK)) as UB. rewrite length_le8 in UB.
    pose proof (proj1 P40) as BN. pose proof (proj1 P32) as BK. pose proof (proj1 UK) as BXk.
    destruct CK as (_ & _ & FKs & BKs). rewrite map_app in BKs. cbn [map] in BKs.
    assert (F1 : Forall (fun c => 0 <= c < 256) (fst (nth n (tkids t) ([], JNull))))
      by (eapply Forall_impl; [|exact FKs]; intros ? ?; cbv beta in *; lia).
    assert (F2 : Forall (fun c => 0 <= c < 256) sv)
      by (eapply Forall_impl; [|exact FS]; intros ? ?; cbv beta in *; lia).
    assert (AL : Z.land (keys + 8 * Z.of_nat n) 7 = 0) by (apply ev_al8; Z.div_mod_to_equations; lia).
    assert (AL2 : Z.land (8 * Z.of_nat n + keys) 7 = 0) by (rewrite Z.add_comm; exact AL).
    apply (proj1 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
    zstep. first [if_true | if_false | idtac].
    zstep. if_cases HT1; [exfalso; trapx HT1|].
    zstep. zstep.
    zstep. zstep. zstep. if_cases HT2; [exfalso; trapx HT2|].
    zstep. zstep. zstep. zstep. if_cases HT3; [exfalso; trapx HT3|].
    zstep. if_cases HT4; [exfalso; trapx HT4|].
    zstep. if_cases HT5; [exfalso; trapx HT5|].
    zstep. zstep. zstep. if_cases HT6; [exfalso; trapx HT6|].
    zstep. zstep. zstep.
    pose proof SCC as S1. unfold strcmp_contract, STRCMP in S1.
    eapply evt_cut.
    { eapply S1 with (sx := map (Z_to_bv 8) (fst (nth n (tkids t) ([], JNull)))) (sy := map (Z_to_bv 8) sv).
      - rewrite unsigned_lit by lia. exact BKs.
      - apply ev_no0. exact FKs.
      - rewrite unsigned_lit by lia. exact BS.
      - apply ev_no0. exact FS. }
    intros ms' PO. destruct PO as (r2 & x11 & x12 & x13 & E2 & HR2). subst ms'.
    replace (ret_pc (Z_to_bv 64 0x14b94)) with (Z_to_bv 64 0x14b94) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (proj2 (ev_fr_jl _ _ _ _ _ _ _ _)) in FR.
    zstep. if_cases H2.
    + zify_cond H2.
      assert (Er : r2 = Z_to_bv 64 0) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
      pose proof (ev_map_inj _ _ F1 F2 (proj1 HR2 Er)) as EQ.
      apply (K m3 dlA); [exact HFI|exact SS|exact DLA|].
      split; [left; assumption|]. intros [?|[_ ?]]; [assumption|contradiction].
    + zify_cond H2.
      zstep. zstep.
      eapply (K _ 1); [fi_pack; right; reflexivity|exact SS|right; reflexivity|].
      split; [intros _; right; split; [reflexivity|]|intros _; reflexivity].
      intros EQ. assert (Er : r2 = Z_to_bv 64 0) by (apply HR2; rewrite EQ; reflexivity).
      subst r2. rewrite unsigned_lit in H2 by lia. lia.
Qed.

Lemma objn_quote : forall i i1 (n : nat) vv dlA kid fl (w0 w24 w32 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m1 fc' F',
  ev_FI m1 (ev_jl w0 (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 125) w24 w32) i1 (d + 1) dlA fc' F' -> stk rsegs m1 scr (scr + len + 1) -> 0 <= i <= i1 -> i1 <= len ->
  Z.of_nat n <= len -> X i1 = skip (X i) ->
  ev_VV true vv -> ev_KID vv n kid fl -> (dlA = 0 \/ dlA = 1) ->
  (ex_name true (X i) = None -> ex_V d (X i0) = None) ->
  (forall nm i' m'' dlB (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word),
     ex_name true (X i) = Some (nm, X i') -> i < i' <= len ->
     ev_FI m'' (ev_jl w0 (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 125) w24 w32) i' (d + 1) dlB fc' F' -> stk rsegs m'' scr (scr + len + 1) -> (dlB = 0 \/ dlB = 1) ->
     (dlB = 1 <-> dlA = 1 \/ (fl = 1 /\ fst (nth n (tkids t) ([], JNull)) <> nm)) ->
     evt rsegs ev_Q (MS (mkR z1 (Z_to_bv 64 (SP + -144)) gp tp z5 z6 z7 (Z_to_bv 64 q) (Z_to_bv 64 vv) z10 z11 z12
      z13 z14 z15 z16 z17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 123) (Z_to_bv 64 44)
      (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123)
      (Z_to_bv 64 (-1)) (Z_to_bv 64 fl) z28 z29 z30 z31) F' (Z_to_bv 64 0x14bd0) fc' None m'' (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 vv) y10 y11 y12
      y13 y14 y15 y16 y17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 123) (Z_to_bv 64 44)
      (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123)
      (Z_to_bv 64 (-1)) (Z_to_bv 64 fl) y28 y29 y30 y31) F' (Z_to_bv 64 0x14b1c) fc' None m1 (seg_rom rsegs)).
Proof.
  intros i i1 n vv dlA kid fl w0 w24 w32 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m1 fc' F' HFI SS Hi Hi' Hnl HX VV KID DLA HN K.
  fi_open HFI.
  pose proof AQW as WQ. unfold ex_apart in WQ. pose proof AQX as WX. unfold ex_apart in WX.
  pose proof AQS as WS. unfold ex_apart in WS. pose proof AXS as WXS. unfold ex_apart in WXS.
  pose proof AXW as WXW. unfold ex_apart in WXW.
  pose proof (ev_bx m1 MU) as BXm.
  zstep. zstep. zstep. zstep. if_cases H1.
  { zify_cond H1. eapply ev_epi; [exact HFI|]. unfold exvu_b.ev_FIN. rewrite HN; [split; [reflexivity|lia]|].
    apply objn_name_nil. rewrite <- HX. apply ev_X_end. lia. }
  zify_cond H1.
  zstep. if_cases HT; [exfalso; trapx HT|].
  pose proof (ev_read_x m1 x0 x i1 BXm ltac:(lia)) as RX.
  pose proof (ev_X_cons x i1 ltac:(lia)) as XC.
  remember (nth (Z.to_nat i1) x (Z_to_bv 8 0)) as b eqn:Eb.
  pose proof (ev_byte_range b) as Rb.
  rewrite XC in HX.
  zstep. zstep. zstep. if_cases H2.
  { zify_cond H2. eapply ev_epi; [exact HFI|]. unfold exvu_b.ev_FIN. rewrite HN; [split; [reflexivity|lia]|].
    apply (objn_name_nq _ (bv_unsigned b) (X (i1 + 1))); [symmetry; exact HX|lia]. }
  zify_cond H2. rewrite H2 in HX.
  assert (XS : map bv_unsigned (skipn (S (Z.to_nat i1)) x) = X (i1 + 1)) by (unfold ev_X; do 2 f_equal; lia).
  assert (SPU : bv_unsigned (Z_to_bv 64 (SP + -144)) = SP + -144) by (apply unsigned_lit; lia).
  pose proof (ev_stk_wr m1 scr (scr + len + 1) SS ltac:(lia)) as SWR.
  replace (scr + len + 1 - scr) with (len + 1) in SWR by lia.
  assert (SSo : stk rsegs m1 scr (scr + len + 1) /\ wr_at rsegs m1 scr (len + 1)) by (split; assumption).
  clear SS SWR.
  pose proof (ev_rw_wr _ _ _ RP) as WRq. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in WRq.
  zstep. zstep.
  pose proof ESC as E1. unfold ex_string_contract, EX_STRING_K in E1.
  eapply evt_cut.
  { eapply E1 with (q := q) (x0 := x0) (i0 := i1) (scr := scr) (lo := lo) (x := x).
    - reflexivity.
    - exact QA.
    - exact (ev_rw8_bytes _ _ _ RP).
    - exact (ev_rw8_bytes _ _ _ RE).
    - exact (ev_rw8_bytes _ _ _ RS).
    - exact WRq.
    - exact BXm.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact (proj2 SSo).
    - destruct WS as [?|[?|[?|?]]]; [lia|lia|right; lia|left; lia].
    - destruct WXS as [?|[?|[?|?]]]; [lia|lia|right; lia|left; lia].
    - rewrite SPU. exact ST.
    - rewrite SPU. lia.
    - rewrite SPU. Z.div_mod_to_equations. lia.
    - rewrite SPU. destruct WQ as [?|[?|[?|?]]]; [lia|lia|right; lia|left; lia].
    - rewrite SPU. destruct WXW as [?|[?|[?|?]]]; [lia|lia|right; lia|left; lia].
    - rewrite SPU. right. lia.
    - exact MI. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & E &
    WMc & MIc & STc & PM).
  subst ms'. rewrite SPU in STc, PM.
  replace (ret_pc (Z_to_bv 64 0x14b44)) with (Z_to_bv 64 0x14b44) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  rewrite XS in PM. change (fst (fst (jr_string (X (i1 + 1)) []))) with (run0 (jr_string (X (i1 + 1)))) in PM.
  destruct (run0 (jr_string (X (i1 + 1)))) as [[sv rest]|] eqn:JS.
  - destruct PM as (Er & MUc & (c & SC & Erest & BQ) & BS). subst r.
    destruct (ex_string_rest _ _ _ JS) as (c' & SC' & Er' & Hc' & Hsv & HB).
    rewrite SC in SC'. injection SC' as <-.
    pose proof (HB (ev_bytes_X x (i1 + 1))) as HBs.
    assert (LY : Z.of_nat (length (X (i1 + 1))) = len - (i1 + 1)) by (apply ev_X_len; lia).
    transport_after_call rsegs m1 m'' MUc WMc.
    destruct SSo as (SSa & SWa).
    replace (x0 + i1 + Z.of_nat c + 2) with (x0 + (i1 + Z.of_nat c + 2)) in BQ by lia.
    pose proof (ev_rw8_mk _ _ _ BQ WRq) as RP2.
    assert (SS2 : stk rsegs m'' scr (scr + len + 1)).
    { apply (objn_stk_fill _ m1 m'' scr (scr + len + 1) scr _ SSa MUc WMc BS).
      intros z Hz. rewrite length_app, length_map. cbn [length].
      destruct (Z_lt_le_dec z (scr + Z.of_nat (length sv) + 1)) as [Hz1|Hz1]; [right; lia|left].
      cbn [outside]. split; [destruct WS as [?|[?|[?|?]]]; lia|]. split; [lia|]. split; [lia|exact I]. }
    assert (Er2 : rest = X (i1 + Z.of_nat c + 2)) by (rewrite Erest, objn_X_skip by lia; f_equal; lia).
    assert (HFI2 : ev_FI m'' (ev_jl w0 (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 125) w24 w32) (i1 + Z.of_nat c + 2) (d + 1) dlA fc' F') by fi_pack.
    zstep. first [if_true | if_false | idtac].
    eapply (objn_key (i1 + Z.of_nat c + 2) n vv dlA kid fl sv w0 w24 w32);
      [exact HFI2|exact SS2|exact BS|exact HBs|exact VV|exact KID|exact DLA|exact Hnl|].
    intros m4 dlB u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 FI4 SS4 DLB HDB.
    eapply (objn_after i (i1 + Z.of_nat c + 2) n vv dlB kid fl sv); [exact FI4|exact SS4|lia| |exact HN|].
    + rewrite <- Er2. apply (objn_name_str _ (X (i1 + 1))); [symmetry; exact HX|exact JS].
    + intros i3 Hi3 EN3 m5 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 FI5 SS5.
      eapply (K sv (i3 + 1) m5 dlB); [exact EN3|lia|exact FI5|exact SS5|exact DLB|exact HDB].
  - destruct PM as (Er & MUc). subst r.
    transport_after_call rsegs m1 m'' MUc WMc.
    assert (HFI2 : ev_FI m'' (ev_jl w0 (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 125) w24 w32) i1 (d + 1) dlA fc' F') by fi_pack.
    zstep. first [if_true | if_false | idtac].
    eapply ev_epi; [exact HFI2|]. unfold exvu_b.ev_FIN. rewrite HN; [split; [reflexivity|lia]|].
    apply (objn_name_str0 _ (X (i1 + 1))); [symmetry; exact HX|exact JS].
Qed.

Lemma ev_obj_name : forall i (n : nat) vv dlA kid fl (w0 w24 w32 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m' fc' F',
  ev_FI m' (ev_jl w0 (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 125) w24 w32) i (d + 1) dlA fc' F' -> stk rsegs m' scr (scr + len + 1) -> 0 <= i <= len -> d + 1 <= 32 ->
  Z.of_nat n <= len -> ev_VV true vv -> ev_KID vv n kid fl -> (dlA = 0 \/ dlA = 1) ->
  (ex_name true (X i) = None -> ex_V d (X i0) = None) ->
  (forall nm i' m'' dlB (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word),
     ex_name true (X i) = Some (nm, X i') -> i < i' <= len ->
     ev_FI m'' (ev_jl w0 (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 125) w24 w32) i' (d + 1) dlB fc' F' -> stk rsegs m'' scr (scr + len + 1) -> (dlB = 0 \/ dlB = 1) ->
     (dlB = 1 <-> dlA = 1 \/ (fl = 1 /\ fst (nth n (tkids t) ([], JNull)) <> nm)) ->
     evt rsegs ev_Q (MS (mkR z1 (Z_to_bv 64 (SP + -144)) gp tp z5 z6 z7 (Z_to_bv 64 q) (Z_to_bv 64 vv) z10 z11 z12
      z13 z14 z15 z16 z17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 123) (Z_to_bv 64 44)
      (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123)
      (Z_to_bv 64 (-1)) (Z_to_bv 64 fl) z28 z29 z30 z31) F' (Z_to_bv 64 0x14bd0) fc' None m'' (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 vv) y10 y11 y12
      y13 y14 y15 y16 y17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 123) (Z_to_bv 64 44)
      (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123)
      (Z_to_bv 64 (-1)) (Z_to_bv 64 fl) y28 y29 y30 y31) F' (Z_to_bv 64 0x14b14) fc' None m' (seg_rom rsegs)).
Proof.
  intros i n vv dlA kid fl w0 w24 w32 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' fc' F' HFI SS Hi Hd Hnl VV KID DLA HN K.
  zstep. zstep.
  eapply (ev_ws i 0x14b1c); [lia|reflexivity|lia|exact HFI|].
  intros i1 m1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 FI1 Hr HX MU1 WM1.
  eapply (objn_quote i i1 n vv dlA kid fl w0 w24 w32);
    [exact FI1| |lia|lia|exact Hnl|exact HX|exact VV|exact KID|exact DLA|exact HN|exact K].
  eapply stk_transport_disjoint; [exact SS|exact MU1|exact WM1|cbn [disjoint_from]; split; [ap AQS; lia|exact I]].
Qed.

End EV.
