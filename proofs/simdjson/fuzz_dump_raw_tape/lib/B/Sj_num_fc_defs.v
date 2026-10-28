(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition FCB_GTOP : Z := 0x6ce000.

Record fcbenv : Type := mkFcbEnv {
  q_ra : word; q_sp : word; q_gp : word; q_tp : word;
  q_s0 : word; q_s1 : word; q_s2 : word; q_s3 : word; q_s4 : word; q_s5 : word;
  q_s6 : word; q_s7 : word; q_s8 : word; q_s9 : word; q_s10 : word; q_s11 : word;
  q_A : Z; q_FIRST : Z; q_LAST : Z; q_OUT : Z; q_lo : Z; q_spq : Z; q_f : Z; q_txt : list byte; q_m0 : mem }.
Notation q_SP E := (bv_unsigned (q_sp E)).
Notation q_TL E := (Z.of_nat (length (q_txt E))).
Notation q_S E := (q_f E / 8 + 2147450880)%Z.

Record fcb_ok (E : fcbenv) : Prop := mkFcbOk {
  fo_room : (q_lo E + SPB_STACK <= q_SP E)%Z;
  fo_top : (q_SP E + 16 <= USTACK_TOP)%Z;
  fo_spq : (q_SP E - 272 <= q_spq E <= q_SP E - 256 /\ q_spq E mod 32 = 0)%Z;
  fo_f : (q_f E mod 64 = 0 /\ FCB_GTOP <= q_f E /\ q_f E + 1016 <= q_lo E)%Z;
  fo_fsh : (q_f E + 1016 <= q_S E \/ q_S E + 127 <= q_f E)%Z;
  fo_fs0 : (FCB_GTOP <= q_S E /\ q_S E + 127 <= q_lo E)%Z;
  fo_txr : (0 < q_A E /\ q_A E + q_TL E <= q_lo E /\ q_TL E < NUM_TXT_MAX)%Z;
  fo_flr : (q_A E <= q_FIRST E /\ q_FIRST E < q_LAST E /\ q_LAST E <= q_A E + q_TL E)%Z;
  fo_tsep : ((q_A E + q_TL E <= q_f E \/ q_f E + 1024 <= q_A E) /\ (q_A E + q_TL E <= q_S E \/ q_S E + 128 <= q_A E))%Z;
  fo_out : (q_OUT E mod 8 = 0 /\ q_SP E <= q_OUT E /\ q_OUT E + 8 <= USTACK_TOP)%Z }.

Definition fcb_W (E : fcbenv) : list (Z * Z) :=
  [(q_lo E, q_spq E + 152); (q_f E, q_f E + 8); (q_f E + 32, q_f E + 536); (q_S E + 4, q_S E + 67); (q_OUT E, q_OUT E + 8)]%Z.

Definition fcb_prov (E : fcbenv) : Prop :=
  (forall m', munch (fcb_W E) (q_m0 E) m' -> wmono bsegs (q_m0 E) m' -> shz m' (8 * (q_FIRST E / 8)) (q_LAST E - 8 * (q_FIRST E / 8)))%Z /\
  (forall m', munch (fcb_W E) (q_m0 E) m' -> wmono bsegs (q_m0 E) m' -> shz m' (q_OUT E) 8) /\
  (forall m', munch (fcb_W E) (q_m0 E) m' -> wmono bsegs (q_m0 E) m' -> shz m' (q_spq E) 152) /\
  (forall m', munch (fcb_W E) (q_m0 E) m' -> wmono bsegs (q_m0 E) m' -> shz m' 0x2b4e0 160) /\
  (forall m', munch (fcb_W E) (q_m0 E) m' -> wmono bsegs (q_m0 E) m' -> shz m' 0x28c20 10416) /\
  (forall m', munch (fcb_W E) (q_m0 E) m' -> wmono bsegs (q_m0 E) m' -> shz m' 0x2b5a0 640).

Definition fcb_spill (E : fcbenv) (c0 c8 c16 c24 c32 c40 c48 c56 : word) : list cell :=
  [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 (Z_to_bv 64 (q_f E))].

Definition FCPINV (E : fcbenv) (mm : mem) (c0 c8 c16 c24 c32 c40 c48 c56 : word) : Prop :=
  rw_cells bsegs mm (q_spq E) (fcb_spill E c0 c8 c16 c24 c32 c40 c48 c56) /\
  (exists jp, rw_cells bsegs mm (q_spq E + 72) [CB 72 jp]) /\
  (exists jd, rw_cells bsegs mm (q_spq E + 144) [CB 8 jd]) /\
  (exists h0, rw_cells bsegs mm (q_f E) [CB 8 h0]) /\
  (exists jb, rw_cells bsegs mm (q_f E + 32) [CB 504 jb]) /\
  (exists js, rw_cells bsegs mm (q_f E / 8 + 2147450884) [CB 63 js]) /\
  (exists v, rw_cells bsegs mm (q_OUT E) [C8 v]) /\
  bytes_at bsegs mm (q_A E) (q_txt E) /\
  mem_inv bsegs mm /\ munch (fcb_W E) (q_m0 E) mm /\ wmono bsegs (q_m0 E) mm /\ stk bsegs mm (q_lo E) (q_spq E).

Ltac fcp_open H :=
  let jp := fresh "jp" in let jd := fresh "jd" in let h0 := fresh "h0" in let jb := fresh "jb" in let js := fresh "js" in let v := fresh "v" in
  destruct H as (SPILL & (jp & PNS) & (jd & DGC) & (h0 & HDR) & (jb & BIG) & (js & BSH) & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold fcb_spill in SPILL; unfold fcb_W in MU;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
Ltac fcp_forget_obj :=
  lazymatch goal with
  | |- exists j, rw_cells ?s ?m ?A [CB ?n j] =>
      first [ eexists; eassumption
            | lazymatch goal with
              | H : rw_cells s m A ?cs |- _ =>
                  let j := fresh "j" in let Hj := fresh "Hj" in
                  destruct (rw_cells_forget s m A cs H) as [j Hj]; exists j; exact Hj
              end ]
  end.
Ltac fcp_close :=
  lazymatch goal with
  | |- FCPINV _ _ _ _ _ _ _ _ _ _ =>
      split; [unfold fcb_spill; eassumption|]; split; [fcp_forget_obj|]; split; [fcp_forget_obj|]; split; [fcp_forget_obj|]; split; [fcp_forget_obj|];
      split; [fcp_forget_obj|]; split; [eexists; eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; [unfold fcb_W; eassumption|]; split; eassumption
  end.

Definition fcb_pns (q : Z) (w lm : word) (nb : Z) (vb : byte) (tm : Z) (j5 : list byte) (IP IL FPT FL : Z) (er : word) (j4 : list byte) : list cell :=
  [C8 (Z_to_bv 64 q); C8 w; C8 lm; C1 (Z_to_bv 8 nb); C1 vb; C1 (Z_to_bv 8 tm); CB 5 j5;
   C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL); C4 er; CB 4 j4].
Definition FCINV (E : fcbenv) (mm : mem) (bg : bool) (js : list byte) (c0 c8 c16 c24 c32 c40 c48 c56 : word) (q : Z) (w lm : word) (nb tm IP IL FPT FL : Z) : Prop :=
  rw_cells bsegs mm (q_spq E) (fcb_spill E c0 c8 c16 c24 c32 c40 c48 c56) /\
  (exists vb j5 er j4, rw_cells bsegs mm (q_spq E + 72) (fcb_pns q w lm nb vb tm j5 IP IL FPT FL er j4)) /\ (0 <= nb <= 1)%Z /\ (0 <= tm <= 1)%Z /\
  (exists jd, rw_cells bsegs mm (q_spq E + 144) [CB 8 jd]) /\
  (exists h0, rw_cells bsegs mm (q_f E) [CB 8 h0]) /\
  (bg = true -> exists jb, rw_cells bsegs mm (q_f E + 32) [CB 504 jb]) /\
  rw_cells bsegs mm (q_f E / 8 + 2147450884) [CB 63 js] /\
  (exists v, rw_cells bsegs mm (q_OUT E) [C8 v]) /\
  bytes_at bsegs mm (q_A E) (q_txt E) /\
  mem_inv bsegs mm /\ munch (fcb_W E) (q_m0 E) mm /\ wmono bsegs (q_m0 E) mm /\ stk bsegs mm (q_lo E) (q_spq E).
Ltac fc_open H :=
  let vb := fresh "vb" in let j5 := fresh "j5" in let er := fresh "er" in let j4 := fresh "j4" in
  let jd := fresh "jd" in let h0 := fresh "h0" in let v := fresh "v" in
  destruct H as (SPILL & (vb & j5 & er & j4 & PNS) & ?NBR & ?TMR & (jd & DGC) & (h0 & HDR) & BIGP & BSH & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold fcb_spill in SPILL; unfold fcb_pns in PNS; unfold fcb_W in MU;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB;
  lazymatch type of BIGP with
  | true = true -> _ => let jb := fresh "jb" in destruct (BIGP eq_refl) as [jb BIG]; clear BIGP
  | false = true -> _ => clear BIGP
  end.
Ltac fc_close :=
  lazymatch goal with
  | |- FCINV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      split; [unfold fcb_spill; eassumption|]; split; [do 4 eexists; unfold fcb_pns; eassumption|]; split; [lia|]; split; [lia|];
      split; [fcp_forget_obj|]; split; [fcp_forget_obj|];
      split; [first [ intros BGF; discriminate BGF | intros _; fcp_forget_obj ]|];
      split; [eassumption|]; split; [eexists; eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; [unfold fcb_W; eassumption|]; split; eassumption
  end.

Definition fcb_spans (E : fcbenv) (IP IL FPT FL : Z) : Prop :=
  (q_FIRST E <= IP /\ 0 <= IL /\ IP + IL <= q_LAST E /\ (FPT = 0 \/ (q_FIRST E <= FPT /\ 0 <= FL /\ FPT + FL <= q_LAST E)))%Z.

Lemma fcb_merge_all : forall (m : mem) A cs, rw_cells bsegs m A cs -> rw_cells bsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof (rw_cells_merge bsegs m A [] cs []) as M. rewrite app_nil_r in M. cbn [app] in M. exact (M H).
Qed.

Notation FCS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
  (MS (mkR xra (Z_to_bv 64 (q_spq E)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom bsegs)).

Ltac fcb_env OK :=
  let ROOM := fresh "ROOM" in let TOP := fresh "TOP" in let SPQ := fresh "SPQ" in let FF := fresh "FF" in let FSH := fresh "FSH" in let FS0 := fresh "FS0" in
  let TXR := fresh "TXR" in let FLR := fresh "FLR" in let TSEP := fresh "TSEP" in let OUTR := fresh "OUTR" in
  destruct OK as [ROOM TOP SPQ FF FSH FS0 TXR FLR TSEP OUTR];
  unfold SPB_STACK, NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, FCB_GTOP, NUM_TXT_MAX, USTACK_TOP in *;
  lazymatch goal with E : fcbenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR end.
Ltac fcb_prov PV :=
  let SHPT := fresh "SHPT" in let SHPO := fresh "SHPO" in let SHPF := fresh "SHPF" in let SHPL := fresh "SHPL" in
  pose proof PV as (SHPT & SHPO & SHPF & SHPL & _); unfold fcb_W in SHPT, SHPO; clear SHPF SHPL.

Ltac fcb_prov_tbl PV :=
  let SHPT := fresh "SHPT" in let SHPO := fresh "SHPO" in let SHPP := fresh "SHPP" in let SHPC := fresh "SHPC" in
  pose proof PV as (SHPT & SHPO & _ & _ & SHPP & SHPC); unfold fcb_W in SHPT, SHPO, SHPP, SHPC.
