(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require PropExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec FP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg F_memcpy F_memset.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegCall SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import SegLibBr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3. Import ST.
Open Scope Z_scope.

Module MMU.
Definition V (n : nat) : expr := EVar n.

(* [comment removed for export] *)
Definition hmH (M : word -> option byte) : Prop := mem_inv usegs M.
Definition hmA (_ : Z) : Prop := True.
Definition hmC (_ _ : Z) : Prop := True.
Definition hmR (rom : word -> option byte) : Prop := rom = seg_rom usegs.
Lemma HMC_sub : forall lo hi lo' hi', hmC lo hi -> lo <= lo' -> hi' <= hi -> hmC lo' hi'.
Proof. intros; exact I. Qed.
Lemma HMF : forall E W M M', SP.wins_client hmC E W -> hmH M -> PIosRegs.wrel usegs M M' ->
  (forall x : word, SP.outside_wins E W (bv_unsigned x) -> M' x = M x) -> hmH M'.
Proof. intros E W M M' _ H HW _. exact (wrel_mem_inv usegs _ _ HW H). Qed.

(* [comment removed for export] *)
Definition env_ext (E : env) (n : nat) (l : list word) : env :=
  Env (fun v => if Nat.ltb v n then ev E v else nth (v - n) l (Z_to_bv 64 0)) (eb E).

Lemma env_ext_lt : forall E n l v, (v < n)%nat -> ev (env_ext E n l) v = ev E v.
Proof. intros E n l v H. cbn [env_ext ev]. apply Nat.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma env_ext_ge : forall E n l j, ev (env_ext E n l) (n + j) = nth j l (Z_to_bv 64 0).
Proof.
  intros E n l j. cbn [env_ext ev]. destruct (Nat.ltb (n + j) n) eqn:H; [apply Nat.ltb_lt in H; lia|].
  f_equal. lia.
Qed.

Lemma gagree_ext : forall G E n l, (G <= n)%nat -> SP.gagree G E (env_ext E n l).
Proof. intros G E n l H j Hj. symmetry. apply env_ext_lt. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MC_pre_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 19; V 20; V 21; V 4; V 5; V 16; V 17; V 18; V 22; V 23; V 24; V 25; V 26;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 27; V 28; V 29; V 30].
Definition MC_pre_kn (kk : nat) (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc; KBlob (SA (V 17) 0) (V 18) kk; KWr (SA (V 16) 0) (V 18); KUnk (SA (V 16) 0) (V 18);
   KDisj (SA (V 17) 0) (V 18) (SA (V 16) 0) (V 18)].
Definition MC_pre (kk : nat) (rpc : Z) : tmpl := TM 0x79f84 MC_pre_regs (MC_pre_kn kk rpc) 31%nat (ELit 0) 0%nat.
Definition MC_post_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 31; V 32; V 33; V 4; V 5; V 16; V 34; V 35; V 36; V 37; V 38; V 39; V 40;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 41; V 42; V 43; V 44].
Definition MC_post (kk : nat) (rpc : Z) : tmpl := TM rpc MC_post_regs [KBlob (SA (V 16) 0) (V 18) kk] 45%nat (ELit 0) 0%nat.
Definition MC_W : list SP.win := [(V 16, 0, V 18)].
Definition MCP (kk : nat) (rpc : Z) : SP.summ := SP.SUMR 19 (MC_pre kk rpc) [MC_post kk rpc] MC_W None None.

Section Bridge.
Variable GP : nat -> list word -> (word -> option byte) -> Prop.

Lemma mcp_lib : forall kk rpc, 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SLib.summ_libH usegs GP hmH hmA hmC hmR (MCP kk rpc).
Proof.
  intros kk rpc Hr0 Hr2 E M rom R F fc HRom _ _ HHM HRF HR HK _ HZ.
  unfold hmR in HRom. subst rom. cbn [MCP SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know MC_pre MC_post TM] in *.
  rewrite (regs_ok_canon E MC_pre_regs R HRF HR). cbn [MC_pre_regs sr_get nth edenot].
  unfold know_ok in HK. unfold MC_pre_kn in HK.
  inversion HK as [|? ? K0 HK1]; subst. inversion HK1 as [|? ? K1 HK2]; subst. inversion HK2 as [|? ? K2 HK3]; subst.
  inversion HK3 as [|? ? K3 HK4]; subst. inversion HK4 as [|? ? K4 _]; subst.
  cbn [kentry_ok V edenot] in K0.
  destruct (SLB.kn_blob_bytes usegs E M _ _ _ _ K1) as (SRC & LEN & S0 & S1). cbn [V edenot] in SRC, LEN, S0, S1. rewrite Z.add_0_r in SRC, S0, S1.
  destruct (SLB.kn_rw_CB usegs E M _ _ _ K2 K3) as (junk & DST). cbn [V edenot] in DST. rewrite Z.add_0_r in DST.
  assert (SEP : bv_unsigned (ev E 17) + bv_unsigned (ev E 18) <= bv_unsigned (ev E 16)
                \/ bv_unsigned (ev E 16) + bv_unsigned (ev E 18) <= bv_unsigned (ev E 17)).
  { cbn [kentry_ok] in K4. unfold estart, elenZ in K4. cbn [a_base a_off V edenot] in K4. lia. }
  pose proof (memcpy_spec (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 19) (ev E 20) (ev E 21) (ev E 4) (ev E 5) (ev E 16) (ev E 17) (ev E 18)
                (ev E 22) (ev E 23) (ev E 24) (ev E 25) (ev E 26) (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12)
                (ev E 13) (ev E 14) (ev E 15) (ev E 27) (ev E 28) (ev E 29) (ev E 30) F fc M (eb E kk) junk SRC LEN DST SEP HHM)
    as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel usegs _ _ Hrun) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & DST' & SRC').
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact (SLB.msteps_mstepsF_none usegs E _ _ Hrun)|].
  set (E' := env_ext E 31 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 31)%nat -> ev E' v = ev E v) by (intros v Hv; apply env_ext_lt; exact Hv).
  exists (MC_post kk rpc), E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (ev E 16) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [MC_post TM t_pc]. f_equal.
    assert (Hra : ev E 0 = Z_to_bv 64 rpc) by (apply bv_eq; rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); lia).
    rewrite Hra. apply ret_pc_even; assumption. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split.
  { apply regs_ok_mkR. reflexivity. }
  split.
  { constructor; [|constructor].
    assert (E16 : ev E' 16 = ev E 16) by (apply EQ; lia). assert (E18 : ev E' 18 = ev E 18) by (apply EQ; lia).
    apply (SLB.kx_blob usegs E' m' (V 16) 0 (V 18) kk); cbn [V edenot]; rewrite ?E16, ?E18, ?Z.add_0_r.
    - pose proof (SLB.urange (ev E 16)); lia.
    - destruct (SLB.kn_wr_at usegs E M _ _ _ K2) as (W1 & W2 & _). cbn [V edenot] in W2. rewrite Z.add_0_r in W2. exact W2.
    - pose proof (SLB.urange (ev E 16)); lia.
    - cbn [E' env_ext eb]. exact LEN.
    - intros i Hi. apply (SC.wrel_grows usegs _ _ HW). pose proof (SLB.kn_defined usegs E M (V 16) 0 (V 18) K3 i) as D0.
      cbn [V edenot] in D0. rewrite Z.add_0_r in D0. exact (D0 Hi).
    - cbn [E' env_ext eb]. destruct DST' as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
  split; [constructor|].
  split; [apply gagree_ext; cbn [MCP SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  split; [exact MI'|].
  cbn [SP.frame_ok MCP SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. cbn [map MC_W SP.win_den edenot V]. rewrite Z.add_0_r. exact MU.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MCU_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc; KUnk (SA (V 17) 0) (V 18); KWr (SA (V 16) 0) (V 18); KUnk (SA (V 16) 0) (V 18);
   KDisj (SA (V 17) 0) (V 18) (SA (V 16) 0) (V 18)].
Definition MCU_pre (rpc : Z) : tmpl := TM 0x79f84 MC_pre_regs (MCU_pre_kn rpc) 31%nat (ELit 0) 0%nat.
Definition MCU_post (rpc : Z) : tmpl := TM rpc MC_post_regs [KUnk (SA (V 16) 0) (V 18)] 45%nat (ELit 0) 0%nat.
Definition MCPU (rpc : Z) : SP.summ := SP.SUMR 19 (MCU_pre rpc) [MCU_post rpc] MC_W None None.

Lemma mcpu_lib : forall rpc, 0 <= rpc < 2^64 -> rpc mod 2 = 0 -> SLib.summ_libH usegs GP hmH hmA hmC hmR (MCPU rpc).
Proof.
  intros rpc Hr0 Hr2 E M rom R F fc HRom _ _ HHM HRF HR HK _ HZ.
  unfold hmR in HRom. subst rom. cbn [MCPU SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know MCU_pre MCU_post TM] in *.
  rewrite (regs_ok_canon E MC_pre_regs R HRF HR). cbn [MC_pre_regs sr_get nth edenot].
  unfold know_ok in HK. unfold MCU_pre_kn in HK.
  inversion HK as [|? ? K0 HK1]; subst. inversion HK1 as [|? ? K1 HK2]; subst. inversion HK2 as [|? ? K2 HK3]; subst.
  inversion HK3 as [|? ? K3 HK4]; subst. inversion HK4 as [|? ? K4 _]; subst.
  cbn [kentry_ok V edenot] in K0.
  destruct (SLB.kn_bytes_of_unk usegs E M _ _ _ K1) as (src & SRC & LEN). cbn [V edenot] in SRC, LEN. rewrite Z.add_0_r in SRC.
  destruct (SLB.kn_rw_CB usegs E M _ _ _ K2 K3) as (junk & DST). cbn [V edenot] in DST. rewrite Z.add_0_r in DST.
  assert (SEP : bv_unsigned (ev E 17) + bv_unsigned (ev E 18) <= bv_unsigned (ev E 16)
                \/ bv_unsigned (ev E 16) + bv_unsigned (ev E 18) <= bv_unsigned (ev E 17)).
  { cbn [kentry_ok] in K4. unfold estart, elenZ in K4. cbn [a_base a_off V edenot] in K4. lia. }
  pose proof (memcpy_spec (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 19) (ev E 20) (ev E 21) (ev E 4) (ev E 5) (ev E 16) (ev E 17) (ev E 18)
                (ev E 22) (ev E 23) (ev E 24) (ev E 25) (ev E 26) (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12)
                (ev E 13) (ev E 14) (ev E 15) (ev E 27) (ev E 28) (ev E 29) (ev E 30) F fc M src junk SRC LEN DST SEP HHM)
    as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel usegs _ _ Hrun) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & DST' & SRC').
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact (SLB.msteps_mstepsF_none usegs E _ _ Hrun)|].
  set (E' := env_ext E 31 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 31)%nat -> ev E' v = ev E v) by (intros v Hv; apply env_ext_lt; exact Hv).
  exists (MCU_post rpc), E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (ev E 16) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [MCU_post TM t_pc]. f_equal.
    assert (Hra : ev E 0 = Z_to_bv 64 rpc) by (apply bv_eq; rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); lia).
    rewrite Hra. apply ret_pc_even; assumption. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split; [apply regs_ok_mkR; reflexivity|].
  split.
  { constructor; [|constructor].
    assert (E16 : ev E' 16 = ev E 16) by (apply EQ; lia). assert (E18 : ev E' 18 = ev E 18) by (apply EQ; lia).
    apply (kentry_ok_unk_grows usegs E' M m' _ _ (SC.wrel_grows usegs _ _ HW)).
    destruct K3 as (Hfl & Hd). split.
    - unfold flat, estart, elenZ in *. cbn [a_base a_off V edenot] in *. rewrite E16, E18. exact Hfl.
    - intros i Hi. unfold estart, elenZ in *. cbn [a_base a_off V edenot] in *. rewrite E16 in *. rewrite E18 in Hi. exact (Hd i Hi). }
  split; [constructor|].
  split; [apply gagree_ext; cbn [MCPU SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  split; [exact MI'|].
  cbn [SP.frame_ok MCPU SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. cbn [map MC_W SP.win_den edenot V]. rewrite Z.add_0_r. exact MU.
Qed.

Theorem mcpu_ok : forall rpc, 0 <= rpc < 2^64 -> rpc mod 2 = 0 -> SP.summ_okH usegs GP hmH hmA hmC hmR (MCPU rpc).
Proof. intros rpc H1 H2. apply SLib.summ_of_libH. exact (mcpu_lib rpc H1 H2). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MS_pre_regs (c : Z) : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 19; V 20; V 21; V 4; V 5; V 16; ELit c; V 18; V 22; V 23; V 24; V 25; V 26;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 27; V 28; V 29; V 30].
Definition MS_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc; KWr (SA (V 16) 0) (V 18); KUnk (SA (V 16) 0) (V 18)].
Definition MS_pre (c rpc : Z) : tmpl := TM 0x7a504 (MS_pre_regs c) (MS_pre_kn rpc) 31%nat (ELit 0) 0%nat.
Definition MS_post (c rpc : Z) : tmpl := TM rpc MC_post_regs [KFill (SA (V 16) 0) (V 18) c] 45%nat (ELit 0) 0%nat.
Definition MSP (c rpc : Z) : SP.summ := SP.SUMR 19 (MS_pre c rpc) [MS_post c rpc] MC_W None None.

Lemma msp_lib : forall c rpc, 0 <= c < 256 -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SLib.summ_libH usegs GP hmH hmA hmC hmR (MSP c rpc).
Proof.
  intros c rpc Hc Hr0 Hr2 E M rom R F fc HRom _ _ HHM HRF HR HK _ HZ.
  unfold hmR in HRom. subst rom. cbn [MSP SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know MS_pre MS_post TM] in *.
  rewrite (regs_ok_canon E (MS_pre_regs c) R HRF HR).
  unfold know_ok in HK. unfold MS_pre_kn in HK.
  inversion HK as [|? ? K0 HK1]; subst. inversion HK1 as [|? ? K2 HK2]; subst. inversion HK2 as [|? ? K3 _]; subst.
  cbn [kentry_ok V edenot] in K0.
  destruct (SLB.kn_rw_CB usegs E M _ _ _ K2 K3) as (junk & DST). cbn [V edenot] in DST. rewrite Z.add_0_r in DST.
  pose proof (memset_spec (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 19) (ev E 20) (ev E 21) (ev E 4) (ev E 5) (ev E 16) (Z_to_bv 64 c) (ev E 18)
                (ev E 22) (ev E 23) (ev E 24) (ev E 25) (ev E 26) (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12)
                (ev E 13) (ev E 14) (ev E 15) (ev E 27) (ev E 28) (ev E 29) (ev E 30) F fc M junk DST HHM)
    as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel usegs _ _ Hrun) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & DST').
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact (SLB.msteps_mstepsF_none usegs E _ _ Hrun)|].
  set (E' := env_ext E 31 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 31)%nat -> ev E' v = ev E v) by (intros v Hv; apply env_ext_lt; exact Hv).
  exists (MS_post c rpc), E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (ev E 16) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [MS_post TM t_pc]. f_equal.
    assert (Hra : ev E 0 = Z_to_bv 64 rpc) by (apply bv_eq; rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); lia).
    rewrite Hra. apply ret_pc_even; assumption. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split; [apply regs_ok_mkR; reflexivity|].
  split.
  { constructor; [|constructor].
    assert (E16 : ev E' 16 = ev E 16) by (apply EQ; lia). assert (E18 : ev E' 18 = ev E 18) by (apply EQ; lia).
    destruct (SLB.kn_wr_at usegs E M _ _ _ K2) as (W1 & W2 & _). cbn [V edenot] in W1, W2. rewrite Z.add_0_r in W1, W2.
    destruct DST' as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite Z_to_bv_unsigned, bv_wrap_small in B by (unfold bv_modulus; cbn; lia). rewrite Z.mod_small in B by lia.
    cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off V edenot]. rewrite ?E16, ?E18, ?Z.add_0_r.
    pose proof (SLB.urange (ev E 16)) as R16. pose proof (SLB.urange (ev E 18)) as R18.
    split; [unfold flat, estart, elenZ; cbn [a_base a_off V edenot]; rewrite ?E16, ?E18; lia|].
    intros i Hi. destruct B as (B1 & B2 & HB). specialize (HB (Z.to_nat i)). rewrite repeat_length in HB.
    specialize (HB ltac:(lia)). rewrite Z2Nat.id in HB by lia. unfold mrd, wa in HB.
    pose proof (SLB.kn_defined usegs E M (V 16) 0 (V 18) K3 i) as D0. cbn [V edenot] in D0. rewrite Z.add_0_r in D0.
    pose proof (SC.wrel_grows usegs _ _ HW _ (D0 Hi)) as D1. unfold wa in D1.
    destruct (m' (Z_to_bv 64 (bv_unsigned (ev E 16) + i))) as [x|]; [|contradiction].
    rewrite HB. rewrite nth_error_repeat by lia. reflexivity. }
  split; [constructor|].
  split; [apply gagree_ext; cbn [MSP SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  split; [exact MI'|].
  cbn [SP.frame_ok MSP SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. cbn [map MC_W SP.win_den edenot V]. rewrite Z.add_0_r. exact MU.
Qed.

(* [comment removed for export] *)
Theorem mcp_ok : forall kk rpc, 0 <= rpc < 2^64 -> rpc mod 2 = 0 -> SP.summ_okH usegs GP hmH hmA hmC hmR (MCP kk rpc).
Proof. intros kk rpc H1 H2. apply SLib.summ_of_libH. exact (mcp_lib kk rpc H1 H2). Qed.
Theorem msp_ok : forall c rpc, 0 <= c < 256 -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 -> SP.summ_okH usegs GP hmH hmA hmC hmR (MSP c rpc).
Proof. intros c rpc H0 H1 H2. apply SLib.summ_of_libH. exact (msp_lib c rpc H0 H1 H2). Qed.
End Bridge.
End MMU.
Print Assumptions MMU.mcp_ok.
Print Assumptions MMU.msp_ok.
Print Assumptions MMU.mcpu_ok.
