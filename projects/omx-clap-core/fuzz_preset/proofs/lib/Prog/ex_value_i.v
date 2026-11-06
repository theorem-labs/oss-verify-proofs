From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct strtod_c ex_value_c ex_word_c ex_string_c strcmp_c bcmp_c memcpy_c ex_value_m ex_value_b ex_value_w ex_value_k.
Import ListNotations.
Open Scope Z_scope.

Ltac slia ::= first [ exact I | repeat split; lia1 ].

Definition ev_hid (P : Prop) : Prop := P.
Ltac ev_stash := repeat match goal with H : ?T |- _ =>
  lazymatch T with
  | ev_hid _ => fail
  | _ \/ _ => change T with (ev_hid T) in H
  | _ <-> _ => change T with (ev_hid T) in H
  end end.

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
Local Abbreviation ev_ws_a := (ex_value_w.ev_ws_a ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_ws_2 := (ex_value_w.ev_ws_2 ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_ws_3 := (ex_value_w.ev_ws_3 ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_ws_4 := (ex_value_w.ev_ws_4 ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_ws_5 := (ex_value_w.ev_ws_5 ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).
Local Abbreviation ev_close := (ex_value_k.ev_close ESC EWC SCC BCC MCC SDC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x lblk t D canary ev HTP QA QG RQ0 BX X0 XE XL I0 DD DL SS0 SG SGd SW TV ST0 LOW SA SB SG2 AQX AQS AXS AQW AXW AXE TO GG0 GQ0 GE0 MI0 TM0 IHV).

Ltac ap H := let H' := fresh "A" in pose proof H as H'; unfold ex_apart in H'.
Ltac fi_pack := unfold ex_value_b.ev_FI; rewrite ?ev_rec_iff; repeat (first [ eassumption | apply conj | eexists ]).
Ltac fi_open HFI := let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in let FR := fresh "FR" in
  let ST := fresh "ST" in let EV := fresh "EV" in let REC := fresh "REC" in let DL' := fresh "DL'" in
  let FRM := fresh "FRM" in let FK := fresh "FK" in let ev' := fresh "ev'" in
  pose proof HFI as (MU & WM & MI & FR & ST & (ev' & EV) & REC & DL' & FRM & FK);
  apply ev_rec_iff in REC; destruct REC as (RP & RE & RD & RS & RF); unfold ex_value_b.ev_W in MU; unfold ex_value_b.ev_SAVED in FR.
Ltac epi_go := eapply ev_epi; [fi_pack|unfold ex_value_b.ev_FIN].
Ltac fi_pack2 := unfold ex_value_b.ev_FI; rewrite ?ev_rec_iff; repeat (first [ eassumption | apply conj | eexists ]).

Ltac ev_fipack := try unfold ev_hid in *; fi_pack.

Lemma ev_item : forall (o : bool) i (n cap : nat) acc vv dlB kid fl nm
    (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) m' j fc' F',
  ev_FI m' j i (d + 1) dlB fc' F' -> stk rsegs m' scr (scr + len + 1) -> i0 < i <= len -> d + 1 <= 32 ->
  ev_VV o vv -> ev_KID vv n kid fl -> (dlB = 0 \/ dlB = 1) -> n = length acc -> Z.of_nat n < i ->
  (forall u dlC, (dlC = 0 \/ dlC = 1) -> (dlC = 1 <-> dlB = 1 \/ (kid <> 0 /\ snd (nth n (tkids t) ([], JNull)) <> u)) ->
     ev_DI o vv (S n) (rev acc ++ [(nm, u)]) dlC) ->
  ev_US o (rev acc ++ [(nm, JNull)]) ->
  ex_V d (X i0) = match ex_V (d + 1) (X i) with
    | None => None
    | Some (u, r) =>
        match skip r with
        | c :: r1 => if c =? 44 then ex_L (S (Z.to_nat d)) o (S n) (ex_cap n cap) ((nm, u) :: acc) r1
                     else if c =? closer o then Some (mk o (rev ((nm, u) :: acc)), r1) else None
        | [] => None
        end
    end ->
  (forall i' m'' j' dl'' u (F'' : bvmap 5 word) (fc'' : bv 32) (w1 w5 w6 w7 w11 w12 w14 w15 w16 w17 w19 w26 w28 w29 w30
       w31 : word),
     i < i' <= len -> ev_FI m'' j' i' (d + 1) dl'' fc'' F'' -> stk rsegs m'' scr (scr + len + 1) ->
     ev_DI o vv (S n) (rev acc ++ [(nm, u)]) dl'' ->
     ex_V d (X i0) = ex_L (S (Z.to_nat d)) o (S n) (ex_cap n cap) ((nm, u) :: acc) (X i') ->
     evt rsegs ev_Q (ev_HEAD o vv (S n) w1 w5 w6 w7 w11 w12 w14 w15 w16 w17 w19 w26 w28 w29 w30 w31 F'' fc'' m'' i')) ->
  evt rsegs ev_Q (MS (mkR z1 (Z_to_bv 64 (SP + -128)) gp tp z5 z6 z7 (Z_to_bv 64 q) (Z_to_bv 64 vv) z10 z11 z12 z13 z14
    z15 z16 z17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid) (Z_to_bv 64 (if o then 123 else 91)) (Z_to_bv 64 (closer o))
    (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 123) (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 fl) (Z_to_bv 64 4294977024)
    z28 z29 z30 z31) F' (Z_to_bv 64 0x14810) fc' None m' (seg_rom rsegs)).
Proof.
  intros o i n cap acc vv dlB kid fl nm z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m' j fc' F'
    HFI SS Hi Hd VV KID DLB Hn Hni DIA US HM K.
  pose proof HFI as (MU0 & _).
  destruct (ev_kid_ok vv n kid fl m' KID MU0) as (Dk & TVk & TOk & KR). clear MU0.
  fi_open HFI. ap AQW. ap AQX.
  assert (SPU : bv_unsigned (Z_to_bv 64 (SP + -128)) = SP + -128) by (apply unsigned_lit; lia1).
  zstep. zstep. zstep.
  pose proof (IHV (Z_to_bv 64 0x1481c) (Z_to_bv 64 (SP + -128)) gp tp z5 z6 z7 (Z_to_bv 64 q) (Z_to_bv 64 vv)
    (Z_to_bv 64 q) (Z_to_bv 64 kid) z12 z13 z14 z15 z16 z17 (Z_to_bv 64 (-1)) (Z_to_bv 64 kid)
    (Z_to_bv 64 (if o then 123 else 91)) (Z_to_bv 64 (closer o)) (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 123)
    (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 fl) (Z_to_bv 64 4294977024) z28 z29 z30 z31 F' fc' m' q kid x0 i
    (d + 1) dlB scr lo x (fun a k => In (a, k) D) (snd (nth n (tkids t) ([], JNull))) Dk canary ev') as HC.
  specialize (HC ltac:(lia1)). unfold ex_value_spec in HC. cbv zeta in HC.
  unfold ex_value_K, EX_VALUE_FE, EX_VALUE_KC, STRTOD_IMG_LO, STRTOD_GLOBALS_TOP, STRTOD_ERRNO, STRTOD_GOT_GUARD,
    STRTOD_GUARD in HC.
  rewrite SPU in HC.
  replace (SP + -128 - ((33 - (d + 1)) * 128 + 8928)) with (SP - KD) in HC by lia1.
  replace ((33 - (d + 1)) * 128 + 8928) with (KD - 128) in HC by lia1.
  eapply evt_cut.
  { apply HC.
    - reflexivity.
    - reflexivity.
    - exact HTP.
    - apply ev_rec_iff. exact (conj RP (conj RE (conj RD (conj RS RF)))).
    - exact QA.
    - exact QG.
    - exact (ev_bx m' MU).
    - exact X0.
    - exact XE.
    - exact XL.
    - lia1.
    - lia1.
    - exact DLB.
    - exact SS.
    - exact SG.
    - exact SGd.
    - lia1.
    - exact TVk.
    - exact ST.
    - lia1.
    - Z.div_mod_to_equations. lia1.
    - lia1.
    - lia1.
    - exact AQX.
    - exact AQS.
    - exact AXS.
    - apply (ev_apart_sub _ _ _ _ _ _ AQW); lia1.
    - apply (ev_apart_sub _ _ _ _ _ _ AXW); lia1.
    - exact AXE.
    - exact TOk.
    - exact (ev_gg m' MU WM).
    - exact (ev_gq m' MU WM).
    - exact EV.
    - exact MI.
    - exact (ev_tm m' MU).
    - exact FRM. }
  intros ms' PO. unfold ex_value_post in PO.
  destruct PO as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F2 & fc2 & m2 &
    p2 & d2 & dl2 & ev2 & E & FK2 & FRM2 & MU2 & WM2 & MI2 & TM2 & ST2 & EV2 & REC2 & DL2 & RES).
  subst ms'. rewrite SPU in MU2, ST2.
  unfold ex_value_K, EX_VALUE_FE, EX_VALUE_KC, STRTOD_ERRNO in MU2.
  replace (SP + -128 - ((33 - (d + 1)) * 128 + 8928)) with (SP - KD) in MU2 by lia1.
  replace (ret_pc (Z_to_bv 64 0x1481c)) with (Z_to_bv 64 0x1481c) by (symmetry; apply ret_pc_even; [lia1|reflexivity]).
  change (map bv_unsigned (skipn (Z.to_nat i) x)) with (X i) in RES.
  assert (FR2 : rw_cells rsegs m2 (SP + -128) (CB 24 j :: ev_SAVED)).
  { apply (rw_cells_transport rsegs _ m' m2 _ _ FR MU2 WM2). cbn [disjoint_from cells_size csize ex_value_b.ev_SAVED Nat.add].
    repeat split; lia1. }
  assert (MUt : munch ev_W m m2).
  { apply (munch_trans ev_W m m' m2 MU). refine (munch_weaken _ ev_W m' m2 _ MU2).
    unfold sub_fp, ex_value_b.ev_W. intros z Hz. cbn [outside] in Hz |- *. destruct Hz as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _).
    repeat split; lia1. }
  assert (FI2 : ev_FI m2 j p2 d2 dl2 fc2 F2).
  { unfold ex_value_b.ev_FI. exact (conj MUt (conj (wmono_trans rsegs _ _ _ WM WM2) (conj MI2 (conj FR2 (conj ST2
      (conj (ex_intro _ ev2 EV2) (conj REC2 (conj DL2 (conj FRM2 (ev_fkeep_trans _ _ _ FK FK2)))))))))). }
  clear FR.
  zstep.
  destruct (ex_V (d + 1) (X i)) as [[u rest]|] eqn:EV1.
  2:{ destruct RES as (-> & Hp2 & Hd2). if_cases HB; zify_cond HB; [|lia1].
      eapply ev_epi; [exact FI2|]. unfold ex_value_b.ev_FIN. rewrite HM. split; [reflexivity|lia1]. }
  destruct RES as (-> & Hp2 & -> & SS2 & DLiff). if_cases HB; zify_cond HB; [lia1|].
  destruct (ex_V_rest _ _ _ _ EV1) as (Lr & kk & Er).
  destruct (ev_X_tail x i rest ltac:(lia1) (ex_intro _ kk Er)) as (Xr & Hpr).
  rewrite <- Hp2 in Xr, Hpr. clear Er.
  assert (Hrl : (length rest < length (X i))%nat) by exact Lr.
  pose proof (ev_X_len x i ltac:(lia1)) as LXi.
  assert (Hp2i : i < p2) by lia1.
  clear HC HFI SS KID TVk TOk KR FR2 MUt REC2 HB.
  ev_stash.
  clear RP RE RD RS RF. fi_open FI2. ap AQS. ap AQW. ap AQX.
  zstep. zstep.
  assert (AT : forall iw m3 (w11 w14 : word), ev_FI m3 j iw (d + 1) dl2 fc2 F2 -> stk rsegs m3 scr (scr + len + 1) ->
     p2 <= iw <= len -> X iw = skip rest ->
     evt rsegs ev_Q (MS (mkR (Z_to_bv 64 0x1481c) (Z_to_bv 64 (SP + -128)) gp tp t0' t1' t2' (Z_to_bv 64 q)
       (Z_to_bv 64 vv) (Z_to_bv 64 (x0 + len)) w11 a2' (Z_to_bv 64 (x0 + iw)) w14 a5' a6' a7' (Z_to_bv 64 (-1))
       (Z_to_bv 64 kid) (Z_to_bv 64 (if o then 123 else 91)) (Z_to_bv 64 (closer o)) (Z_to_bv 64 (Z.of_nat n))
       (Z_to_bv 64 123) (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 fl) (Z_to_bv 64 4294977024) t3' t4' t5' t6')
       F2 (Z_to_bv 64 0x1484c) fc2 None m3 (seg_rom rsegs))).
  { intros iw m3 w11 w14 FI3 SS3 Hiw HX.
    try rewrite EV1 in HM. cbv beta iota in HM. rewrite <- HX in HM.
    clear RP RE RD RS RF. fi_open FI3. ev_stash. ap AQW. ap AQX.
    zstep.
    if_cases H1; zify_cond H1.
    { eapply ev_epi; [ev_fipack|]. unfold ex_value_b.ev_FIN. rewrite HM, (ev_X_end x iw) by lia1. split; [reflexivity|lia1]. }
    pose proof (ev_bx m3 (proj1 FI3)) as BX3.
    pose proof (ev_read_x m3 x0 x iw BX3 ltac:(lia1)) as RX.
    pose proof (ev_X_cons x iw ltac:(lia1)) as XC.
    remember (nth (Z.to_nat iw) x (Z_to_bv 8 0)) as c eqn:Ec.
    pose proof (ev_byte_range c) as Rc.
    rewrite XC in HM.
    zstep. zstep.
    if_cases H2; zify_cond H2.
    - zstep.
      if_cases H3; zify_cond H3.
      + eapply ev_epi; [ev_fipack|]. unfold ex_value_b.ev_FIN. rewrite HM.
        rewrite (proj2 (Z.eqb_neq _ _)) by lia1. rewrite (proj2 (Z.eqb_neq _ _)) by (destruct o; cbn in H3 |- *; lia1).
        split; [reflexivity|lia1].
      + zstep. zstep. zstep.
        replace (x0 + iw + 1) with (x0 + (iw + 1)) in * by lia1.
        first [replace (Z_to_bv 64 (Z.of_nat n + 1)) with (Z_to_bv 64 (Z.of_nat (S n))) by (f_equal; lia1)
               | replace (Z_to_bv 64 (Z.of_nat n) + Z_to_bv 64 1)%bv with (Z_to_bv 64 (Z.of_nat (S n)))
                   by (rewrite lit_add_lit; f_equal; lia1) | idtac].
        eapply (ev_close o (S n) (rev ((nm, u) :: acc)) vv dl2 (iw + 1)); [ev_fipack|exact SS3|lia1|lia1|exact VV|
          rewrite length_rev; cbn [length]; lia1|lia1| | |].
        * cbn [rev]. eapply ev_US_app. exact US.
        * cbn [rev]. try unfold ev_hid in *; apply DIA; assumption.
        * rewrite HM. rewrite (proj2 (Z.eqb_neq _ _)) by lia1.
          rewrite (proj2 (Z.eqb_eq _ _)) by (destruct o; cbn in H3 |- *; lia1). reflexivity.
    - zstep. zstep. zstep.
      replace (x0 + iw + 1) with (x0 + (iw + 1)) in * by lia1.
      rewrite (proj2 (Z.eqb_eq _ _)) in HM by lia1.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (K (iw + 1) mm j dl2 u F2 fc2) as K1 end.
      unfold ex_value_b.ev_HEAD in K1.
      zstep.
      first [replace (Z_to_bv 64 (Z.of_nat n + 1)) with (Z_to_bv 64 (Z.of_nat (S n))) by (f_equal; lia1)
               | replace (Z_to_bv 64 (Z.of_nat n) + Z_to_bv 64 1)%bv with (Z_to_bv 64 (Z.of_nat (S n)))
                   by (rewrite lit_add_lit; f_equal; lia1) | idtac].
      if_cases H4; zify_cond H4.
      + assert (V0 : vv <> 0) by (intro E0; subst vv; apply H4; reflexivity).
        rewrite (proj2 (Z.eqb_neq _ _) V0) in K1.
        eapply K1; [lia1|ev_fipack|exact SS3| |exact HM].
        try unfold ev_hid in *; apply DIA; assumption.
      + zstep.
        assert (V0 : vv = 0).
        { destruct VV as [(-> & _)|(-> & Hv & _)]; [reflexivity|]. pose proof ev_vr as Rv.
          rewrite Z.mod_small in H4 by lia. exact H4. }
        subst vv.
        eapply K1; [lia1|ev_fipack|exact SS3| |exact HM].
        try unfold ev_hid in *; apply DIA; assumption. }
  zstep. if_cases H5; zify_cond H5.
  - apply (AT p2 m2); [ev_fipack|exact SS2|lia1|].
    rewrite Xr, (ev_X_end x p2) by lia1. reflexivity.
  - eapply ev_ws_5; [reflexivity|lia1|ev_fipack|].
    intros iw m3 y11' FI3 Hr HX MU3 WM3.
    apply (AT iw m3); [exact FI3| |lia1|rewrite HX, <- Xr; reflexivity].
    eapply stk_transport_disjoint; [exact SS2|exact MU3|exact WM3|cbn [disjoint_from]; split; [lia1|exact I]].
Qed.

End EV.
