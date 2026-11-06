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

Lemma ev_ws_a : forall (n : nat) (i : Z) (y1 y5 y6 y7 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29
    y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32) m' j dep dl',
  Z.to_nat (len - i) = n -> 0 <= i < len -> ev_FI m' j i dep dl' fc' F' ->
  (forall i1 m'' (y14' : word), ev_FI m'' j i1 dep dl' fc' F' -> i <= i1 <= len -> X i1 = skip (X i) ->
     munch [(q, q + 8)] m' m'' -> wmono rsegs m' m'' ->
     evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) y9 (Z_to_bv 64 (x0 + len))
       (Z_to_bv 64 32) (Z_to_bv 64 4294977024) (Z_to_bv 64 (x0 + i1)) y14' y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25
       y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x14438) fc' None m'' (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) y9 (Z_to_bv 64 (x0 + len))
       (Z_to_bv 64 32) (Z_to_bv 64 4294977024) (Z_to_bv 64 (x0 + i)) y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25
       y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x14418) fc' None m' (seg_rom rsegs)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros i y1 y5 y6 y7 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 F' fc' m' j dep dl'
    Hn Hi HFI K.
  fi_open HFI. ap AQW. ap AQX.
  pose proof (ev_bx m' MU) as BXm.
  pose proof (ev_read_x m' x0 x i BXm Hi) as RX.
  pose proof (ev_X_cons x i Hi) as XC.
  remember (nth (Z.to_nat i) x (Z_to_bv 8 0)) as b eqn:Eb.
  pose proof (ev_byte_range b) as Rb.
  pose proof (munch_refl [(q, q + 8)] m') as MUl. pose proof (wmono_refl rsegs m') as WMl.
  zstep. zstep.
  if_cases H1.
  { zify_cond H1. apply (K i m'); [exact HFI|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. rewrite (ev_ws_big b H1). reflexivity. }
  zify_cond H1. zstep. zstep. zstep.
  if_cases H2.
  { zify_cond H2. pose proof (ev_ws_mask b H1) as WS. rewrite (proj2 (Z.eqb_eq _ _) H2) in WS.
    apply (K i m'); [exact HFI|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. destruct (ws (bv_unsigned b)); [discriminate|reflexivity]. }
  zify_cond H2. pose proof (ev_ws_mask b H1) as WS. Time rewrite (proj2 (Z.eqb_neq _ _) H2) in WS.
  assert (WSb : ws (bv_unsigned b) = true) by (destruct (ws (bv_unsigned b)); [reflexivity|discriminate]).
  Time zstep. Time zstep. Time zstep.
  if_cases H3.
  - zify_cond H3. replace (x0 + i + 1) with (x0 + (i + 1)) in * by lia.
    eapply (IHn (n - 1)%nat); [lia|lia|lia|fi_pack|].
    intros i1 m'' y14' FI' Hr HX MU' WM'. apply (K i1 m'' y14' FI'); [lia| | |].
    + rewrite HX, XC. cbn [skip]. rewrite WSb. reflexivity.
    + eapply munch_trans; eassumption.
    + eapply wmono_trans; eassumption.
  - zify_cond H3. replace (x0 + i + 1) with (x0 + (i + 1)) in * by lia.
    apply (K (i + 1) m0); [fi_pack|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. rewrite WSb. rewrite (ev_X_end x (i + 1)) by lia. reflexivity.
Qed.

Lemma ev_ws_2 : forall (n : nat) (i : Z) (y1 y5 y6 y7 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32) m' j dep dl',
  Z.to_nat (len - i) = n -> 0 <= i < len -> ev_FI m' j i dep dl' fc' F' ->
  (forall i1 m'' (y14' : word), ev_FI m'' j i1 dep dl' fc' F' -> i <= i1 <= len -> X i1 = skip (X i) ->
     munch [(q, q + 8)] m' m'' -> wmono rsegs m' m'' ->
     evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) y9 (Z_to_bv 64 (x0 + len)) (Z_to_bv 64 32) (Z_to_bv 64 4294977024) (Z_to_bv 64 (x0 + i1)) y14' y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x14688) fc' None m'' (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) y9 (Z_to_bv 64 (x0 + len)) (Z_to_bv 64 32) (Z_to_bv 64 4294977024) (Z_to_bv 64 (x0 + i)) y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x14668) fc' None m' (seg_rom rsegs)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros i y1 y5 y6 y7 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 F' fc' m' j dep dl'
    Hn Hi HFI K.
  fi_open HFI. ap AQW. ap AQX.
  pose proof (ev_bx m' MU) as BXm.
  pose proof (ev_read_x m' x0 x i BXm Hi) as RX.
  pose proof (ev_X_cons x i Hi) as XC.
  remember (nth (Z.to_nat i) x (Z_to_bv 8 0)) as b eqn:Eb.
  pose proof (ev_byte_range b) as Rb.
  pose proof (munch_refl [(q, q + 8)] m') as MUl. pose proof (wmono_refl rsegs m') as WMl.
  zstep. zstep.
  if_cases H1.
  { zify_cond H1. apply (K i m'); [exact HFI|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. rewrite (ev_ws_big b H1). reflexivity. }
  zify_cond H1. zstep. zstep. zstep.
  if_cases H2.
  { zify_cond H2. pose proof (ev_ws_mask b H1) as WS. rewrite (proj2 (Z.eqb_eq _ _) H2) in WS.
    apply (K i m'); [exact HFI|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. destruct (ws (bv_unsigned b)); [discriminate|reflexivity]. }
  zify_cond H2. pose proof (ev_ws_mask b H1) as WS. Time rewrite (proj2 (Z.eqb_neq _ _) H2) in WS.
  assert (WSb : ws (bv_unsigned b) = true) by (destruct (ws (bv_unsigned b)); [reflexivity|discriminate]).
  Time zstep. Time zstep. Time zstep.
  if_cases H3.
  - zify_cond H3. replace (x0 + i + 1) with (x0 + (i + 1)) in * by lia.
    eapply (IHn (n - 1)%nat); [lia|lia|lia|fi_pack|].
    intros i1 m'' y14' FI' Hr HX MU' WM'. apply (K i1 m'' y14' FI'); [lia| | |].
    + rewrite HX, XC. cbn [skip]. rewrite WSb. reflexivity.
    + eapply munch_trans; eassumption.
    + eapply wmono_trans; eassumption.
  - zify_cond H3. replace (x0 + i + 1) with (x0 + (i + 1)) in * by lia.
    apply (K (i + 1) m0); [fi_pack|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. rewrite WSb. rewrite (ev_X_end x (i + 1)) by lia. reflexivity.
Qed.

Lemma ev_ws_3 : forall (n : nat) (i : Z) (y1 y5 y6 y7 y9 y11 y12 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y26 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32) m' j dep dl',
  Z.to_nat (len - i) = n -> 0 <= i < len -> ev_FI m' j i dep dl' fc' F' ->
  (forall i1 m'' (y11' : word), ev_FI m'' j i1 dep dl' fc' F' -> i <= i1 <= len -> X i1 = skip (X i) ->
     munch [(q, q + 8)] m' m'' -> wmono rsegs m' m'' ->
     evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) y9 (Z_to_bv 64 (x0 + len)) y11' y12 (Z_to_bv 64 (x0 + i1)) y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 (Z_to_bv 64 32) y25 y26 (Z_to_bv 64 4294977024) y28 y29 y30 y31) F' (Z_to_bv 64 0x14788) fc' None m'' (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) y9 (Z_to_bv 64 (x0 + len)) y11 y12 (Z_to_bv 64 (x0 + i)) y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 (Z_to_bv 64 32) y25 y26 (Z_to_bv 64 4294977024) y28 y29 y30 y31) F' (Z_to_bv 64 0x14768) fc' None m' (seg_rom rsegs)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros i y1 y5 y6 y7 y9 y11 y12 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y26 y28 y29 y30 y31 F' fc' m' j dep dl'
    Hn Hi HFI K.
  fi_open HFI. ap AQW. ap AQX.
  pose proof (ev_bx m' MU) as BXm.
  pose proof (ev_read_x m' x0 x i BXm Hi) as RX.
  pose proof (ev_X_cons x i Hi) as XC.
  remember (nth (Z.to_nat i) x (Z_to_bv 8 0)) as b eqn:Eb.
  pose proof (ev_byte_range b) as Rb.
  pose proof (munch_refl [(q, q + 8)] m') as MUl. pose proof (wmono_refl rsegs m') as WMl.
  zstep. zstep.
  if_cases H1.
  { zify_cond H1. apply (K i m'); [exact HFI|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. rewrite (ev_ws_big b H1). reflexivity. }
  zify_cond H1. zstep. zstep. zstep.
  if_cases H2.
  { zify_cond H2. pose proof (ev_ws_mask b H1) as WS. rewrite (proj2 (Z.eqb_eq _ _) H2) in WS.
    apply (K i m'); [exact HFI|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. destruct (ws (bv_unsigned b)); [discriminate|reflexivity]. }
  zify_cond H2. pose proof (ev_ws_mask b H1) as WS. rewrite (proj2 (Z.eqb_neq _ _) H2) in WS.
  assert (WSb : ws (bv_unsigned b) = true) by (destruct (ws (bv_unsigned b)); [reflexivity|discriminate]).
  zstep. zstep. zstep.
  if_cases H3.
  - zify_cond H3. replace (x0 + i + 1) with (x0 + (i + 1)) in * by lia.
    eapply (IHn (n - 1)%nat); [lia|lia|lia|fi_pack|].
    intros i1 m'' y11' FI' Hr HX MU' WM'. apply (K i1 m'' y11' FI'); [lia| | |].
    + rewrite HX, XC. cbn [skip]. rewrite WSb. reflexivity.
    + eapply munch_trans; eassumption.
    + eapply wmono_trans; eassumption.
  - zify_cond H3. replace (x0 + i + 1) with (x0 + (i + 1)) in * by lia.
    apply (K (i + 1) m0); [fi_pack|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. rewrite WSb. rewrite (ev_X_end x (i + 1)) by lia. reflexivity.
Qed.

Lemma ev_ws_4 : forall (n : nat) (i : Z) (y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y26 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32) m' j dep dl',
  Z.to_nat (len - i) = n -> 0 <= i < len -> ev_FI m' j i dep dl' fc' F' ->
  (forall i1 m'' (y12' : word), ev_FI m'' j i1 dep dl' fc' F' -> i <= i1 <= len -> X i1 = skip (X i) ->
     munch [(q, q + 8)] m' m'' -> wmono rsegs m' m'' ->
     evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) y9 (Z_to_bv 64 (x0 + i1)) (Z_to_bv 64 (x0 + len)) y12' y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 (Z_to_bv 64 32) y25 y26 (Z_to_bv 64 4294977024) y28 y29 y30 y31) F' (Z_to_bv 64 0x147f8) fc' None m'' (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) y9 (Z_to_bv 64 (x0 + i)) (Z_to_bv 64 (x0 + len)) y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 (Z_to_bv 64 32) y25 y26 (Z_to_bv 64 4294977024) y28 y29 y30 y31) F' (Z_to_bv 64 0x147d8) fc' None m' (seg_rom rsegs)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros i y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y26 y28 y29 y30 y31 F' fc' m' j dep dl'
    Hn Hi HFI K.
  fi_open HFI. ap AQW. ap AQX.
  pose proof (ev_bx m' MU) as BXm.
  pose proof (ev_read_x m' x0 x i BXm Hi) as RX.
  pose proof (ev_X_cons x i Hi) as XC.
  remember (nth (Z.to_nat i) x (Z_to_bv 8 0)) as b eqn:Eb.
  pose proof (ev_byte_range b) as Rb.
  pose proof (munch_refl [(q, q + 8)] m') as MUl. pose proof (wmono_refl rsegs m') as WMl.
  zstep. zstep.
  if_cases H1.
  { zify_cond H1. apply (K i m'); [exact HFI|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. rewrite (ev_ws_big b H1). reflexivity. }
  zify_cond H1. zstep. zstep. zstep.
  if_cases H2.
  { zify_cond H2. pose proof (ev_ws_mask b H1) as WS. rewrite (proj2 (Z.eqb_eq _ _) H2) in WS.
    apply (K i m'); [exact HFI|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. destruct (ws (bv_unsigned b)); [discriminate|reflexivity]. }
  zify_cond H2. pose proof (ev_ws_mask b H1) as WS. rewrite (proj2 (Z.eqb_neq _ _) H2) in WS.
  assert (WSb : ws (bv_unsigned b) = true) by (destruct (ws (bv_unsigned b)); [reflexivity|discriminate]).
  zstep. zstep. zstep.
  if_cases H3.
  - zify_cond H3. replace (x0 + i + 1) with (x0 + (i + 1)) in * by lia.
    eapply (IHn (n - 1)%nat); [lia|lia|lia|fi_pack|].
    intros i1 m'' y12' FI' Hr HX MU' WM'. apply (K i1 m'' y12' FI'); [lia| | |].
    + rewrite HX, XC. cbn [skip]. rewrite WSb. reflexivity.
    + eapply munch_trans; eassumption.
    + eapply wmono_trans; eassumption.
  - zify_cond H3. replace (x0 + i + 1) with (x0 + (i + 1)) in * by lia.
    apply (K (i + 1) m0); [fi_pack|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. rewrite WSb. rewrite (ev_X_end x (i + 1)) by lia. reflexivity.
Qed.

Lemma ev_ws_5 : forall (n : nat) (i : Z) (y1 y5 y6 y7 y9 y11 y12 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y26 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32) m' j dep dl',
  Z.to_nat (len - i) = n -> 0 <= i < len -> ev_FI m' j i dep dl' fc' F' ->
  (forall i1 m'' (y11' : word), ev_FI m'' j i1 dep dl' fc' F' -> i <= i1 <= len -> X i1 = skip (X i) ->
     munch [(q, q + 8)] m' m'' -> wmono rsegs m' m'' ->
     evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) y9 (Z_to_bv 64 (x0 + len)) y11' y12 (Z_to_bv 64 (x0 + i1)) y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 (Z_to_bv 64 32) y25 y26 (Z_to_bv 64 4294977024) y28 y29 y30 y31) F' (Z_to_bv 64 0x1484c) fc' None m'' (seg_rom rsegs))) ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp y5 y6 y7 (Z_to_bv 64 q) y9 (Z_to_bv 64 (x0 + len)) y11 y12 (Z_to_bv 64 (x0 + i)) y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 (Z_to_bv 64 32) y25 y26 (Z_to_bv 64 4294977024) y28 y29 y30 y31) F' (Z_to_bv 64 0x1482c) fc' None m' (seg_rom rsegs)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros i y1 y5 y6 y7 y9 y11 y12 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y26 y28 y29 y30 y31 F' fc' m' j dep dl'
    Hn Hi HFI K.
  fi_open HFI. ap AQW. ap AQX.
  pose proof (ev_bx m' MU) as BXm.
  pose proof (ev_read_x m' x0 x i BXm Hi) as RX.
  pose proof (ev_X_cons x i Hi) as XC.
  remember (nth (Z.to_nat i) x (Z_to_bv 8 0)) as b eqn:Eb.
  pose proof (ev_byte_range b) as Rb.
  pose proof (munch_refl [(q, q + 8)] m') as MUl. pose proof (wmono_refl rsegs m') as WMl.
  zstep. zstep.
  if_cases H1.
  { zify_cond H1. apply (K i m'); [exact HFI|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. rewrite (ev_ws_big b H1). reflexivity. }
  zify_cond H1. zstep. zstep. zstep.
  if_cases H2.
  { zify_cond H2. pose proof (ev_ws_mask b H1) as WS. rewrite (proj2 (Z.eqb_eq _ _) H2) in WS.
    apply (K i m'); [exact HFI|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. destruct (ws (bv_unsigned b)); [discriminate|reflexivity]. }
  zify_cond H2. pose proof (ev_ws_mask b H1) as WS. Time rewrite (proj2 (Z.eqb_neq _ _) H2) in WS.
  assert (WSb : ws (bv_unsigned b) = true) by (destruct (ws (bv_unsigned b)); [reflexivity|discriminate]).
  Time zstep. Time zstep. Time zstep.
  if_cases H3.
  - zify_cond H3. replace (x0 + i + 1) with (x0 + (i + 1)) in * by lia.
    eapply (IHn (n - 1)%nat); [lia|lia|lia|fi_pack|].
    intros i1 m'' y11' FI' Hr HX MU' WM'. apply (K i1 m'' y11' FI'); [lia| | |].
    + rewrite HX, XC. cbn [skip]. rewrite WSb. reflexivity.
    + eapply munch_trans; eassumption.
    + eapply wmono_trans; eassumption.
  - zify_cond H3. replace (x0 + i + 1) with (x0 + (i + 1)) in * by lia.
    apply (K (i + 1) m0); [fi_pack|lia| |exact MUl|exact WMl].
    rewrite XC. cbn [skip]. rewrite WSb. rewrite (ev_X_end x (i + 1)) by lia. reflexivity.
Qed.

End EV.
