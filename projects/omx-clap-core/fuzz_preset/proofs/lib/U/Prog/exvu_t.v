From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct ex_value_c ex_value_m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strtod_c ex_value_c ex_word_c ex_string_c strcmp_c bcmp_c memcpy_c ex_ws_c exvu_b.
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

Ltac ap H := let H' := fresh "A" in pose proof H as H'; unfold ex_apart in H'.
Ltac fi_pack := unfold exvu_b.ev_FI; rewrite ?ev_rec_iff; repeat (first [ eassumption | apply conj | eexists ]).
Ltac fi_open HFI := let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in let FR := fresh "FR" in
  let ST := fresh "ST" in let EV := fresh "EV" in let REC := fresh "REC" in let DL' := fresh "DL'" in
  let FRM := fresh "FRM" in let FK := fresh "FK" in let ev' := fresh "ev'" in
  pose proof HFI as (MU & WM & MI & FR & ST & (ev' & EV) & REC & DL' & FRM & FK);
  apply ev_rec_iff in REC; destruct REC as (RP & RE & RD & RS & RF); unfold exvu_b.ev_W in MU; unfold exvu_b.ev_SAVED in FR.
Ltac ev_fipack := try unfold ev_hid in *; fi_pack.

Lemma ev_lit : forall (w ty : Z) (W : list byte) (wz : list Z) (u : jv) i1 (y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y20
    y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) m' j fc' F',
  ev_FI m' j i1 d dl fc' F' -> 0 <= i1 < len ->
  ex_word_lit w W -> W = map (Z_to_bv 8) wz -> Forall (fun c => 0 <= c < 256) wz -> wz <> [] ->
  ty = tag u -> (forall t', tag t' = ty -> t' = u) ->
  ex_V d (X i0) = (if prefixb wz (X i1) then Some (u, skipn (length wz) (X i1)) else None) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 v) (Z_to_bv 64 q)
    (Z_to_bv 64 w) (Z_to_bv 64 ty) y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F'
    (Z_to_bv 64 0x14a30) fc' None m' (seg_rom rsegs)).
Proof.
  intros w ty W wz u i1 y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 m' j
    fc' F' HFI Hi HW EW WZ WN Ety HU HV.
  subst W.
  fi_open HFI. ap AQW. ap AQX. ap AQS. ap AXS. ap AXW.
  pose proof (ev_bx m' MU) as BXm. pose proof ev_vr as VR. pose proof (ev_tm m' MU) as TM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (TY : 0 <= ty <= 2) by (rewrite Ety; apply strlit_lit_tag; intros t' Ht'; apply HU; rewrite Ety; exact Ht').
  assert (MT : ex_word_match x i1 (map (Z_to_bv 8) wz) <-> prefixb wz (X i1) = true)
    by (apply strlit_match; [lia1|exact WZ]).
  assert (LX : Z.of_nat (length (X i1)) = len - i1) by (apply ev_X_len; lia1).
  assert (TT : v <> 0 -> bytes_at rsegs m' v (le4 (Z_to_bv 64 (tag t))) /\ 0 <= tag t < 2 ^ 32 /\ ex_word_off sp v 4).
  { intros Hv. destruct (ev_hdr _ _ _ _ _ (ev_tree m' Hv MU)) as (? & ? & ? & ? & ? & ? & (_ & (Tr & Tb) & _)).
    split; [exact Tb|]. split; [exact Tr|]. unfold ex_word_off, EX_WORD_K.
    destruct (TO Hv) as (_ & _ & (Ow & _) & _). unfold ex_apart in Ow. lia1. }
  assert (TT8 : v <> 0 -> v mod 8 = 0 /\ bytes_at rsegs m' v (le4 (Z_to_bv 64 (tag t))) /\ 0 <= tag t < 2 ^ 32 /\
    ex_word_off sp v 4) by (intros Hv; split; [exact (ev_v8 Hv)|exact (TT Hv)]).
  pose proof (ev_rw8_bytes _ _ _ RP) as BP. pose proof (ev_rw8_bytes _ _ _ RE) as BE.
  pose proof (ev_rw_wr _ _ _ RP) as WP. pose proof (ev_rw_wr _ _ _ RF) as WF.
  do 14 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep. zstep.
  eapply evt_cut.
  { eapply EWC with (q := q) (x0 := x0) (i0 := i1) (w := w) (ty := ty) (v := v) (t := tag t) (x := x)
      (W := map (Z_to_bv 8) wz) (lo := lo);
      [reflexivity|reflexivity|reflexivity|reflexivity|exact HW|exact TY|exact QA| |exact WP|exact WF|exact BXm|exact X0|lia1|
       lia1|exact TT8|
       exact MI|exact ST|unfold EX_WORD_K; lia1|unfold ex_word_off, EX_WORD_K; lia1|unfold ex_word_off, EX_WORD_K; lia1].
    apply bytes_at_app. split; [exact BP|]. rewrite length_le8. exact BE. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & E & WMc
    & MIc & STc & PM).
  subst ms'. apply evt_done. unfold exvu_b.ev_Q, ex_value_post.
  unfold EX_WORD_K in PM.
  assert (MU3 : munch [(SP - 64, SP); (q, q + 8); (q + 32, q + 36)] m' m'').
  { destruct PM as [(_ & _ & _ & [(_ & _ & _ & M)|(_ & M)])|(_ & _ & M)];
      (eapply munch_weaken; [|exact M]); unfold sub_fp; cbn [outside]; intros z (H1 & H2 & H3 & _);
      repeat split; assumption. }
  assert (MUt : munch ev_W m m'').
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU3]. unfold sub_fp, exvu_b.ev_W. cbn [outside].
    intros; slia. }
  assert (WMt : wmono rsegs m m'') by (eapply wmono_trans; eassumption).
  pose proof (strlit_stk_mono _ _ _ _ SS0 WMt) as SSt.
  pose proof (ev_tm m'' MUt) as TMt.
  assert (EVt : rw_cells rsegs m'' 0x352a4 [C4 ev']).
  { apply (rw_cells_transport rsegs _ m' m'' _ _ EV MU3 WMc). cbn [disjoint_from cells_size csize]. slia. }
  assert (REt : rw_cells rsegs m'' (q + 8) [C8 (Z_to_bv 64 (x0 + len))]).
  { apply (rw_cells_transport rsegs _ m' m'' _ _ RE MU3 WMc). cbn [disjoint_from cells_size csize]. slia. }
  assert (RDt : rw_cells rsegs m'' (q + 16) [C4 (Z_to_bv 64 d)]).
  { apply (rw_cells_transport rsegs _ m' m'' _ _ RD MU3 WMc). cbn [disjoint_from cells_size csize]. slia. }
  assert (RSt : rw_cells rsegs m'' (q + 24) [C8 (Z_to_bv 64 scr)]).
  { apply (rw_cells_transport rsegs _ m' m'' _ _ RS MU3 WMc). cbn [disjoint_from cells_size csize]. slia. }
  pose proof (wr_at_transport rsegs m' m'' q _ WP WMc) as WPt.
  pose proof (wr_at_transport rsegs m' m'' (q + 32) _ WF WMc) as WFt.
  unfold exvu_b.ev_W in MUt. unfold ex_value_K, EX_VALUE_FE, EX_VALUE_KC, STRTOD_ERRNO.
  destruct PM as [(WMa & Er & BQ & [(Hv & Htn & BF & M)|(Hvt & M)])|(NWM & Er & M)]; subst r.
  - assert (LW : Z.of_nat (length wz) <= len - i1) by (destruct WMa as [L _]; rewrite length_map in L; exact L).
    assert (RPt : rw_cells rsegs m'' q [C8 (Z_to_bv 64 (x0 + (i1 + Z.of_nat (length wz))))]).
    { apply ev_rw8_mk; [|exact WPt]. rewrite length_map in BQ.
      replace (x0 + (i1 + Z.of_nat (length wz))) with (x0 + i1 + Z.of_nat (length wz)) by lia1. exact BQ. }
    assert (RFt : rw_cells rsegs m'' (q + 32) [C4 (Z_to_bv 64 1)]) by (apply ev_rw4_mk; [exact BF|exact WFt]).
    assert (PF : prefixb wz (X i1) = true) by (apply MT; exact WMa).
    assert (FIN : ev_FIN (Z_to_bv 64 0) m'' (i1 + Z.of_nat (length wz)) d 1).
    { unfold exvu_b.ev_FIN. rewrite HV, PF. split; [reflexivity|]. split; [rewrite length_skipn; lia1|]. split; [reflexivity|].
      split; [exact SSt|].
      split; [intros _; right; split; [exact Hv|intros E; apply Htn; rewrite E, Ety; reflexivity]|intros _; reflexivity]. }
    exists t0', t1', t2', (Z_to_bv 64 0), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m'',
      (i1 + Z.of_nat (length wz)), d, 1, ev'.
    split; [reflexivity|]. split; [exact FK|]. split; [exact FRM|]. split; [exact MUt|]. split; [exact WMt|].
    split; [exact MIc|]. split; [exact TMt|]. split; [exact STc|]. split; [exact EVt|].
    split; [apply ev_rec_iff; repeat (first [eassumption | apply conj])|]. split; [right; reflexivity|]. exact FIN.
  - assert (LW : Z.of_nat (length wz) <= len - i1) by (destruct WMa as [L _]; rewrite length_map in L; exact L).
    assert (RPt : rw_cells rsegs m'' q [C8 (Z_to_bv 64 (x0 + (i1 + Z.of_nat (length wz))))]).
    { apply ev_rw8_mk; [|exact WPt]. rewrite length_map in BQ.
      replace (x0 + (i1 + Z.of_nat (length wz))) with (x0 + i1 + Z.of_nat (length wz)) by lia1. exact BQ. }
    assert (RFt : rw_cells rsegs m'' (q + 32) [C4 (Z_to_bv 64 dl)]).
    { apply (rw_cells_transport rsegs _ m' m'' _ _ RF M WMc). cbn [disjoint_from cells_size csize]. slia. }
    assert (PF : prefixb wz (X i1) = true) by (apply MT; exact WMa).
    assert (FIN : ev_FIN (Z_to_bv 64 0) m'' (i1 + Z.of_nat (length wz)) d dl).
    { unfold exvu_b.ev_FIN. rewrite HV, PF. split; [reflexivity|]. split; [rewrite length_skipn; lia1|]. split; [reflexivity|].
      split; [exact SSt|]. split; [intros H; left; exact H|intros [H|[Hv Htu]]; [exact H|exfalso]].
      destruct Hvt as [Hv0|Htt]; [exact (Hv Hv0)|apply Htu; apply HU; exact Htt]. }
    exists t0', t1', t2', (Z_to_bv 64 0), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m'',
      (i1 + Z.of_nat (length wz)), d, dl, ev'.
    split; [reflexivity|]. split; [exact FK|]. split; [exact FRM|]. split; [exact MUt|]. split; [exact WMt|].
    split; [exact MIc|]. split; [exact TMt|]. split; [exact STc|]. split; [exact EVt|].
    split; [apply ev_rec_iff; repeat (first [eassumption | apply conj])|]. split; [exact DL'|]. exact FIN.
  - assert (PF : prefixb wz (X i1) = false).
    { destruct (prefixb wz (X i1)) eqn:P; [exfalso; apply NWM; apply MT; reflexivity|reflexivity]. }
    assert (RPt : rw_cells rsegs m'' q [C8 (Z_to_bv 64 (x0 + i1))]).
    { apply (rw_cells_transport rsegs _ m' m'' _ _ RP M WMc). cbn [disjoint_from cells_size csize]. slia. }
    assert (RFt : rw_cells rsegs m'' (q + 32) [C4 (Z_to_bv 64 dl)]).
    { apply (rw_cells_transport rsegs _ m' m'' _ _ RF M WMc). cbn [disjoint_from cells_size csize]. slia. }
    assert (FIN : ev_FIN (Z_to_bv 64 (-1)) m'' i1 d dl).
    { unfold exvu_b.ev_FIN. rewrite HV, PF. split; [reflexivity|]. lia1. }
    exists t0', t1', t2', (Z_to_bv 64 (-1)), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m'',
      i1, d, dl, ev'.
    split; [reflexivity|]. split; [exact FK|]. split; [exact FRM|]. split; [exact MUt|]. split; [exact WMt|].
    split; [exact MIc|]. split; [exact TMt|]. split; [exact STc|]. split; [exact EVt|].
    split; [apply ev_rec_iff; repeat (first [eassumption | apply conj])|]. split; [exact DL'|]. exact FIN.
Qed.

End EV.
