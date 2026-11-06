From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct strtod_c ex_value_c ex_word_c ex_string_c strcmp_c bcmp_c memcpy_c ex_value_m ex_value_b.
Import ListNotations.
Open Scope Z_scope.

Ltac slia ::= first [ exact I | repeat split; lia1 ].

Set Default Proof Using "All".

Section EV.
Hypotheses (ESC : ex_string_contract) (EWC : ex_word_contract) (SCC : strcmp_contract) (BCC : bcmp_contract)
  (MCC : memcpy_contract) (SDC : strtod_contract).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (m : word -> option byte) (q v x0 i0 d dl scr lo : Z) (x : list byte) (lblk : Z -> Z -> Prop) (t : jv)
  (D : list (Z * Z)) (canary ev : word).

Local Abbreviation SP := (bv_unsigned sp).
Local Abbreviation len := (Z.of_nat (length x)).
Local Abbreviation KD := ((33 - d) * 128 + 8928).
Local Abbreviation X := (ev_X x).

Hypotheses (HTP : tp = Z_to_bv 64 0x34898) (QA : q mod 8 = 0) (QG : 0x56000 <= q)
  (RQ0 : ex_rec m q (x0 + i0) (x0 + len) d scr dl)
  (BX : bytes_at rsegs m x0 x) (X0 : 0 < x0) (XE : x0 + len < 2 ^ 62) (XL : len <= 3 * 2 ^ 20)
  (I0 : 0 <= i0 <= len) (DD : 0 <= d <= 32) (DL : dl = 0 \/ dl = 1)
  (SS0 : stk rsegs m scr (scr + len + 1)) (SG : 4096 <= scr) (SGd : scr + len + 1 <= 0x10000 \/ 0x56000 <= scr)
  (SW : scr + len + 1 <= SP - KD)
  (TV : v = 0 \/ pj_node rsegs m lblk v t D /\ Forall (fun ak => 0 < fst ak) D)
  (ST0 : stk rsegs m lo SP) (LOW : lo <= SP - KD) (SA : SP mod 16 = 0) (SB : SP < 2 ^ 62)
  (SG2 : 0x56000 <= SP - KD)
  (AQX : ex_apart q 40 x0 len) (AQS : ex_apart q 40 scr (len + 1)) (AXS : ex_apart x0 len scr (len + 1))
  (AQW : ex_apart q 40 (SP - KD) KD) (AXW : ex_apart x0 len (SP - KD) KD) (AXE : ex_apart x0 len 0x347f4 4)
  (TO : v <> 0 -> ex_off v D q 40 /\ ex_off v D scr (len + 1) /\ ex_off v D (SP - KD) KD /\
                 ex_off v D 0x347f4 4)
  (GG0 : rw_cells rsegs m 0x234e0 [C8 (Z_to_bv 64 0x54b08)]) (GQ0 : rw_cells rsegs m 0x54b08 [C8 canary])
  (GE0 : rw_cells rsegs m 0x347f4 [C4 ev])
  (MI0 : mem_inv rsegs m) (TM0 : MemNorm.task_mem rsegs m).

Hypothesis IHV : forall (ra' sp' gp' tp' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8'
    s9' s10' s11' t3' t4' t5' t6' : word) (F'' : bvmap 5 word) (fc'' : bv 32) (m'' : word -> option byte)
    (q' v' x0' i0' d' dl' scr' lo' : Z) (x' : list byte) (lblk' : Z -> Z -> Prop) (t' : jv) (D' : list (Z * Z))
    (canary' ev'' : word),
  (Z.to_nat (Z.of_nat (length x') - i0') < Z.to_nat (len - i0))%nat ->
  ex_value_spec ra' sp' gp' tp' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10'
    s11' t3' t4' t5' t6' F'' fc'' m'' q' v' x0' i0' d' dl' scr' lo' x' lblk' t' D' canary' ev''.


Local Abbreviation ev_W := (ex_value_b.ev_W sp q d scr x).
Local Abbreviation ev_Q := (ex_value_b.ev_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x t).
Local Abbreviation ev_SAVED := (ex_value_b.ev_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Abbreviation ev_FI := (ex_value_b.ev_FI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q x0 d scr lo x).
Local Abbreviation ev_FIN := (ex_value_b.ev_FIN v i0 d dl scr x t).
Local Abbreviation ev_D0 := (ex_value_b.ev_D0 v dl t).
Local Abbreviation ev_VV := (ex_value_b.ev_VV v t).
Local Abbreviation ev_US := ex_value_b.ev_US.
Local Abbreviation ev_DI := (ex_value_b.ev_DI v dl t).
Local Abbreviation ev_KID := (ex_value_b.ev_KID m v lblk t D).
Local Abbreviation ev_HEAD := (ex_value_b.ev_HEAD sp gp tp q x0 x).

Local Abbreviation ev_tm := (ex_value_b.ev_tm ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_bx := (ex_value_b.ev_bx ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_gg := (ex_value_b.ev_gg ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_gq := (ex_value_b.ev_gq ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_off_out := (ex_value_b.ev_off_out ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_tree := (ex_value_b.ev_tree ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_epi := (ex_value_b.ev_epi ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_vr := (ex_value_b.ev_vr ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_find_rw := (ex_value_b.strlit_find_rw ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_wv_mrd := (ex_value_b.strlit_wv_mrd ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_stk_mono := (ex_value_b.strlit_stk_mono ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_prefixb := (ex_value_b.strlit_prefixb ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_match := (ex_value_b.strlit_match ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation strlit_lit_tag := (ex_value_b.strlit_lit_tag ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_v_tr := (ex_value_b.ev_v_tr ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_kid_ok := (ex_value_b.ev_kid_ok ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_US_app := (ex_value_b.ev_US_app ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation close_dl := (ex_value_b.close_dl ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_DI_next := (ex_value_b.ev_DI_next ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_skip_map := (ex_value_b.objn_skip_map ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_X_skip := (ex_value_b.objn_X_skip ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_stk_fill := (ex_value_b.objn_stk_fill ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_name_nil := (ex_value_b.objn_name_nil ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_name_nq := (ex_value_b.objn_name_nq ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_name_str0 := (ex_value_b.objn_name_str0 ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation objn_name_str := (ex_value_b.objn_name_str ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_skip_hd := (ex_value_b.ev_skip_hd ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).

Ltac ap H := let H' := fresh "A" in pose proof H as H'; unfold ex_apart in H'.
Ltac fi_pack := unfold ex_value_b.ev_FI; rewrite ?ev_rec_iff; repeat (first [ eassumption | apply conj | eexists ]).
Ltac fi_open HFI := let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in let FR := fresh "FR" in
  let ST := fresh "ST" in let EV := fresh "EV" in let REC := fresh "REC" in let DL' := fresh "DL'" in
  let FRM := fresh "FRM" in let FK := fresh "FK" in let ev' := fresh "ev'" in
  pose proof HFI as (MU & WM & MI & FR & ST & (ev' & EV) & REC & DL' & FRM & FK);
  apply ev_rec_iff in REC; destruct REC as (RP & RE & RD & RS & RF); unfold ex_value_b.ev_W in MU; unfold ex_value_b.ev_SAVED in FR.
Ltac epi_go := eapply ev_epi; [fi_pack|unfold ex_value_b.ev_FIN].
Ltac fi_pack2 := unfold ex_value_b.ev_FI; rewrite ?ev_rec_iff; repeat (first [ eassumption | apply conj | eexists ]).

Lemma ev_str : forall i1 (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30
    y31 : word) m' j fc' F',
  ev_FI m' j i1 d dl fc' F' -> stk rsegs m' scr (scr + len + 1) -> 0 <= i1 < len ->
  X i1 = 34 :: X (i1 + 1) -> ex_V d (X i0) = ex_V d (X i1) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 v) y10 y11 y12 y13
    y14 y15 y16 y17 (Z_to_bv 64 (-1)) y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x1449c) fc'
    None m' (seg_rom rsegs)).
Proof.
  intros i1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 m' j fc' F'
    HFI SS Hi XC HV.
  fi_open HFI. ap AQW. ap AQX. ap AQS. ap AXS. ap AXW.
  pose proof (ev_bx m' MU) as BXm. pose proof ev_vr as VR.
  rewrite XC, ex_V_str in HV.
  assert (XS : map bv_unsigned (skipn (S (Z.to_nat i1)) x) = X (i1 + 1)) by (unfold ev_X; do 2 f_equal; lia).
  assert (SPU : bv_unsigned (Z_to_bv 64 (SP + -128)) = SP + -128) by (apply unsigned_lit; lia).
  pose proof (ev_stk_wr m' scr (scr + len + 1) SS ltac:(lia)) as SWR.
  replace (scr + len + 1 - scr) with (len + 1) in SWR by lia.
  assert (SSo : stk rsegs m' scr (scr + len + 1) /\ wr_at rsegs m' scr (len + 1)) by (split; assumption).
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
    - destruct A1 as [?|[?|[?|?]]]; [lia|lia|right; lia|left; lia].
    - destruct A2 as [?|[?|[?|?]]]; [lia|lia|right; lia|left; lia].
    - rewrite SPU. exact ST.
    - rewrite SPU. lia.
    - rewrite SPU. Z.div_mod_to_equations. lia.
    - rewrite SPU. destruct A as [?|[?|[?|?]]]; [lia|lia|right; lia|left; lia].
    - rewrite SPU. destruct A3 as [?|[?|[?|?]]]; [lia|lia|right; lia|left; lia].
    - rewrite SPU. right. lia.
    - exact MI. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & E &
    WMc & MIc & STc & PM).
  subst ms'. rewrite SPU in STc, PM.
  replace (ret_pc (Z_to_bv 64 83108)) with (Z_to_bv 64 83108) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  rewrite XS in PM. change (fst (fst (jr_string (X (i1 + 1)) []))) with (run0 (jr_string (X (i1 + 1)))) in PM.
  destruct (run0 (jr_string (X (i1 + 1)))) as [[sv rest]|] eqn:JS.
  - destruct PM as (Er & MUc & (c & SC & Erest & BQ) & BS). subst r.
    destruct (ex_string_rest _ _ _ JS) as (c' & SC' & Er' & Hc' & Hsv & HB).
    rewrite SC in SC'. injection SC' as <-.
    pose proof (HB (ev_bytes_X x (i1 + 1))) as HBs.
    assert (LY : Z.of_nat (length (X (i1 + 1))) = len - (i1 + 1)) by (apply ev_X_len; lia).
    transport_after_call rsegs m' m'' MUc WMc.
    destruct SSo as (SSa & SWa).
    pose proof (strlit_stk_mono _ _ _ _ SSa WMc) as SSb. clear SSa SWa.
    assert (RP : rw_cells rsegs m'' q [C8 (Z_to_bv 64 (x0 + (i1 + Z.of_nat c + 2)))]).
    { apply ev_rw8_mk; [|exact WRq]. replace (x0 + (i1 + Z.of_nat c + 2)) with (x0 + i1 + Z.of_nat c + 2) by lia1.
      exact BQ. }
    assert (PV : i1 + Z.of_nat c + 2 = len - Z.of_nat (length rest)) by (rewrite Erest, length_skipn; lia1).
    assert (DL1 : 1 = 0 \/ 1 = 1) by (right; reflexivity).
    clear BQ MUc E1.
    zstep. try if_false.
    zstep. if_cases Hv0; zify_cond Hv0.
    + assert (Hv : v = 0) by (revert Hv0; rewrite ?unsigned_lit by lia1; lia1).
      zstep. zstep.
      eapply ev_epi with (pv := i1 + Z.of_nat c + 2) (dep := d) (dl' := dl); [fi_pack|].
      unfold ex_value_b.ev_FIN. rewrite HV. split; [reflexivity|]. split; [exact PV|]. split; [reflexivity|].
      split; [exact SSb|]. split; [intros H; left; exact H|intros [H|[H _]]; [exact H|exfalso; exact (H Hv)]].
    + assert (Hv : v <> 0) by (revert Hv0; rewrite ?unsigned_lit by lia1; lia1).
      pose proof (ev_tree m'' Hv MU) as TN.
      destruct (ev_hdr _ _ _ _ _ TN) as (num & str & kids & keys & nn & cap & HH).
      pose proof (ev_u32_rd _ _ _ (proj1 (proj2 HH))) as RT.
      pose proof (ev_tag_range t) as TR.
      zstep. rewrite ?ev_sx32 by lia1.
      zstep. zstep. if_cases Ht; zify_cond Ht.
      * assert (Ht4 : tag t <> 4) by (revert Ht; rewrite ?unsigned_lit by lia1; lia1).
        zstep. zstep. zstep. zstep.
        eapply ev_epi with (pv := i1 + Z.of_nat c + 2) (dep := d) (dl' := 1); [fi_pack|].
        unfold ex_value_b.ev_FIN. rewrite HV. split; [reflexivity|]. split; [exact PV|]. split; [reflexivity|].
        split; [exact SSb|].
        split; [intros _; right; split; [exact Hv|intros E; rewrite E in Ht4; exact (Ht4 eq_refl)]|intros _; reflexivity].
      * assert (Ht4 : tag t = 4) by (revert Ht; rewrite ?unsigned_lit by lia1; lia1).
        destruct (ev_tag4 t Ht4) as (s' & Et).
        pose proof TN as TN'. rewrite Et in TN'. cbn [pj_node] in TN'.
        destruct TN' as (_ & _ & num' & str' & kids' & keys' & n' & cap' & HH' & (_ & _ & _ & _ & k & (_ & _ & Fs & Bs) & _)).
        destruct HH' as (_ & _ & _ & U16 & _).
        pose proof (ev_u64_rd _ _ _ U16) as RSTR. destruct U16 as [SR _].
        rewrite map_app in Bs.
        zstep. zstep. zstep.
        eapply evt_cut.
        { eapply SCC with (sx := map (Z_to_bv 8) s') (sy := map (Z_to_bv 8) sv).
          - rewrite unsigned_lit by lia1. exact Bs.
          - exact (ev_no0 s' Fs).
          - rewrite unsigned_lit by lia1. exact BS.
          - exact (ev_no0 sv HBs). }
        intros ms' PO. destruct PO as (r2 & z11 & z12 & z13 & E2 & Hr). subst ms'.
        replace (ret_pc (Z_to_bv 64 0x144c4)) with (Z_to_bv 64 0x144c4) by (symmetry; apply ret_pc_even; [lia1|reflexivity]).
        zstep. if_cases Hc0; zify_cond Hc0.
        -- assert (R0 : r2 = Z_to_bv 64 0) by (apply bv_eq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia1).
           assert (Es : s' = sv).
           { apply ev_map_inj; [eapply Forall_impl; [|exact Fs]; intros a [? ?]; lia1
                               |eapply Forall_impl; [|exact HBs]; intros a [? ?]; lia1
                               |apply Hr; exact R0]. }
           zstep. zstep.
           eapply ev_epi with (pv := i1 + Z.of_nat c + 2) (dep := d) (dl' := dl); [fi_pack|].
           unfold ex_value_b.ev_FIN. rewrite HV. split; [reflexivity|]. split; [exact PV|]. split; [reflexivity|].
           split; [exact SSb|]. rewrite Et, Es.
           split; [intros H; left; exact H|intros [H|[_ H]]; [exact H|exfalso; exact (H eq_refl)]].
        -- assert (Es : s' <> sv).
           { intros Es. subst s'. apply Hc0. rewrite (proj2 Hr eq_refl). reflexivity. }
           zstep. zstep. zstep. zstep.
           eapply ev_epi with (pv := i1 + Z.of_nat c + 2) (dep := d) (dl' := 1); [fi_pack|].
           unfold ex_value_b.ev_FIN. rewrite HV. split; [reflexivity|]. split; [exact PV|]. split; [reflexivity|].
           split; [exact SSb|].
           split; [intros _; right; split; [exact Hv|rewrite Et; intros E; injection E as E; exact (Es E)]|
                   intros _; reflexivity].
  - destruct PM as (Er & MUc). subst r.
    transport_after_call rsegs m' m'' MUc WMc.
    zstep. try if_true.
    eapply ev_epi with (pv := i1) (dep := d) (dl' := dl); [fi_pack|].
    unfold ex_value_b.ev_FIN. rewrite HV. split; [reflexivity|]. lia1.
Qed.

End EV.
