(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit F_gates F_irt F_rip I_printf_lib I_printf_common.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation REAL_vprintf := 664204%Z.
Notation REAL_vfprintf := 638888%Z.
Notation VPRINTF_RESUME := 297420%Z.
Notation VFPRINTF_RESUME := 300348%Z.
Notation FPRINTF_RESUME := 301400%Z.
Notation A0_FMT_E := 84284%Z.
Notation A0_FMT_F1 := 88517%Z.
Notation A0_FMT_F2 := 121494%Z.
Notation A0_FMT_F3 := 121515%Z.
Notation A0_FMT_F4 := 104835%Z.

Definition S_E : Z := 0x1493c.   Definition B_E : list byte := [Z_to_bv 8 37; Z_to_bv 8 100; Z_to_bv 8 10].
Definition S_F1 : Z := 0x159c5.   Definition B_F1 : list byte := [Z_to_bv 8 117; Z_to_bv 8 115; Z_to_bv 8 97; Z_to_bv 8 103; Z_to_bv 8 101; Z_to_bv 8 58; Z_to_bv 8 32; Z_to_bv 8 37; Z_to_bv 8 115; Z_to_bv 8 32; Z_to_bv 8 73; Z_to_bv 8 78; Z_to_bv 8 80; Z_to_bv 8 85; Z_to_bv 8 84; Z_to_bv 8 10].
Definition S_F2 : Z := 0x1da96.   Definition B_F2 : list byte := [Z_to_bv 8 99; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 58; Z_to_bv 8 32; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 110; Z_to_bv 8 110; Z_to_bv 8 111; Z_to_bv 8 116; Z_to_bv 8 32; Z_to_bv 8 111; Z_to_bv 8 112; Z_to_bv 8 101; Z_to_bv 8 110; Z_to_bv 8 32; Z_to_bv 8 37; Z_to_bv 8 115; Z_to_bv 8 10].
Definition S_F3 : Z := 0x1daab.   Definition B_F3 : list byte := [Z_to_bv 8 99; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 58; Z_to_bv 8 32; Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 97; Z_to_bv 8 100; Z_to_bv 8 32; Z_to_bv 8 101; Z_to_bv 8 114; Z_to_bv 8 114; Z_to_bv 8 111; Z_to_bv 8 114; Z_to_bv 8 32; Z_to_bv 8 111; Z_to_bv 8 110; Z_to_bv 8 32; Z_to_bv 8 37; Z_to_bv 8 115; Z_to_bv 8 10].
Definition S_F4 : Z := 0x19983.   Definition B_F4 : list byte := [Z_to_bv 8 99; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 58; Z_to_bv 8 32; Z_to_bv 8 105; Z_to_bv 8 110; Z_to_bv 8 112; Z_to_bv 8 117; Z_to_bv 8 116; Z_to_bv 8 32; Z_to_bv 8 62; Z_to_bv 8 61; Z_to_bv 8 32; Z_to_bv 8 37; Z_to_bv 8 117; Z_to_bv 8 32; Z_to_bv 8 98; Z_to_bv 8 121; Z_to_bv 8 116; Z_to_bv 8 101; Z_to_bv 8 115; Z_to_bv 8 44; Z_to_bv 8 32; Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 115; Z_to_bv 8 101; Z_to_bv 8 100; Z_to_bv 8 10].
Lemma fmtE_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_E (B_E ++ Z_to_bv 8 0 :: []). Proof. img_str S_E B_E. Qed.
Lemma fmtE_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_E. Proof. noz_tac. Qed.
Lemma fmtF1_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_F1 (B_F1 ++ Z_to_bv 8 0 :: []). Proof. img_str S_F1 B_F1. Qed.
Lemma fmtF1_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_F1. Proof. noz_tac. Qed.
Lemma fmtF2_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_F2 (B_F2 ++ Z_to_bv 8 0 :: []). Proof. img_str S_F2 B_F2. Qed.
Lemma fmtF2_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_F2. Proof. noz_tac. Qed.
Lemma fmtF3_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_F3 (B_F3 ++ Z_to_bv 8 0 :: []). Proof. img_str S_F3 B_F3. Qed.
Lemma fmtF3_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_F3. Proof. noz_tac. Qed.
Lemma fmtF4_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_F4 (B_F4 ++ Z_to_bv 8 0 :: []). Proof. img_str S_F4 B_F4. Qed.
Lemma fmtF4_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_F4. Proof. noz_tac. Qed.

Definition pc_postq (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 2320, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q.

Lemma pc_int_specq : forall ra (q : Z) gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo FMT : Z) (fstr pre : list byte) (b37 bc : byte) (post : list byte),
  mem_inv asegs m -> stk asegs m lo q -> lo <= q - 2320 -> 17594333495296 <= lo -> 0 <= q < 2^64 ->
  env_shadow m ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) fstr ->
  1 <= Z.of_nat (length fstr) <= 62 -> (0x10000 <= FMT /\ FMT + Z.of_nat (length fstr) + 1 <= 0x609000) ->
  accessible m FMT (Z.of_nat (length fstr) + 1) -> sh_readable m FMT (Z.of_nat (length fstr) + 1) ->
  fstr = pre ++ b37 :: bc :: post ->
  Forall (fun b : byte => bv_unsigned b <> 37) pre -> Forall (fun b : byte => bv_unsigned b <> 37) post ->
  bv_unsigned b37 = 37 -> intconv (bv_unsigned bc) -> post <> [] ->
  evt asegs (pc_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 (wz FMT) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x48a04) fc None m (seg_rom asegs)).
Proof.
  intros until post. intros MI ST LO KLO Hq (GOT & SHB) FB NOZ FL FIMG ACCF RDF EF NP1 NP2 E37 HC NE.
  assert (U : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (printf_common_int1 ra (wz q)) with (FMT := FMT) (fstr := fstr) (lo := lo); rewrite ?U; try eassumption; reflexivity. }
  intros ms' P. unfold printf_common_post in P. rewrite !U in P. exact P.
Qed.

Lemma pc_str_specq : forall ra (q : Z) gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo FMT : Z) (fstr pre : list byte) (b37 bc : byte) (post : list byte) (AP Sa : Z) (sstr : list byte),
  mem_inv asegs m -> stk asegs m lo q -> lo <= q - 2320 -> 17594333495296 <= lo -> 0 <= q < 2^64 ->
  env_shadow m -> env_layout m ->
  bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) fstr ->
  1 <= Z.of_nat (length fstr) <= 62 -> (0x10000 <= FMT /\ FMT + Z.of_nat (length fstr) + 1 <= 0x609000) ->
  accessible m FMT (Z.of_nat (length fstr) + 1) -> sh_readable m FMT (Z.of_nat (length fstr) + 1) ->
  rw_cells asegs m AP [C8 (wz Sa)] -> (q <= AP /\ AP + 8 <= 2^64) ->
  bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) sstr ->
  (Sa + (Z.of_nat (length sstr) + 1) <= q - 2320 \/ q <= Sa) ->
  cwin Sa (Z.of_nat (length sstr) + 1) -> Sa + (Z.of_nat (length sstr) + 1) < 2^47 -> 0 < Sa ->
  accessible m Sa (Z.of_nat (length sstr) + 1) -> sh_readable m Sa (Z.of_nat (length sstr) + 1) ->
  Z.of_nat (length sstr) + 1 <= 2^43 ->
  fstr = pre ++ b37 :: bc :: post ->
  Forall (fun b : byte => bv_unsigned b <> 37) pre -> Forall (fun b : byte => bv_unsigned b <> 37) post ->
  bv_unsigned b37 = 37 -> sconv (bv_unsigned bc) -> post <> [] ->
  evt asegs (pc_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 (wz FMT) (wz AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x48a04) fc None m (seg_rom asegs)).
Proof.
  intros until sstr. intros MI ST LO KLO Hq (GOT & SHB) (LG & LC) FB NOZ FL FIMG ACCF RDF VAQ SEPV SSTR SNOZ SEPS WINS WIN2 SPOS ACCS RDS NSZ EF NP1 NP2 E37 HC NE.
  assert (U : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
  assert (UA : bv_unsigned (wz AP) = AP) by (apply unsigned_lit; pose proof (rw_cells_bound _ _ _ _ VAQ); lia).
  eapply evt_mono.
  { eapply (printf_common_str1 ra (wz q)) with (FMT := FMT) (fstr := fstr) (lo := lo) (Sa := Sa) (sstr := sstr); rewrite ?U, ?UA; try eassumption; reflexivity. }
  intros ms' P. unfold printf_common_post in P. rewrite !U in P. exact P.
Qed.

Lemma fmtE_split : B_E = [] ++ Z_to_bv 8 37 :: Z_to_bv 8 100 :: [Z_to_bv 8 10]. Proof. reflexivity. Qed.
Ltac n37_tac :=
  apply Forall_forall; let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
  repeat (destruct Hb as [<-|Hb]; [cbv; discriminate|]); destruct Hb.

Definition vprintf_front_post0 (q : Z) (gp tp : word) (ap : Z) (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk : list byte),
    ms' = MS (mkR (wz VPRINTF_RESUME) (wz (q - 48)) gp tp t0 t1 t2 (wz A0_FMT_E) (wz ap) (wz A0_FMT_E) (wz ap) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz REAL_vprintf) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q - 48)
    /\ rw_cells asegs m' (q - 48) [CB 8 junk; C8 (wz ap); C8 (wz ap); C8 s1; C8 s0; C8 ra0].

Lemma vprintf_front_spec : forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (ap lo : Z),
  icpt_env m -> stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 48 - 2400 -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz A0_FMT_E -> a1 = wz ap ->
  accessible m A0_FMT_E 4 -> sh_readable m A0_FMT_E 4 ->
  evt asegs (vprintf_front_post0 q gp tp ap ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_vprintf) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros IE ST KLO LO Q64 MI -> -> ACCF RDF. unfold A0_vprintf.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO' : lo <= q - 48) by lia.
  carve_frame 48%nat ST.
  zstep. do 7 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1 end.
  call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
  clear IE1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
  pose proof (ie_cf _ IE1) as CF1. pose proof (ie_ckpf _ IE1) as CK1. unfold env_cf in CF1. unfold env_ckpf in CK1.
  zstep. lit_branch.
  do 4 zstep.
  cbv beta. zsimp. zstep. zstep. lit_branch.
  do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU' : munch [(lo, q)] m mm, WM' : wmono asegs m mm, MI' : mem_inv asegs mm |- _ =>
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia);
    assert (CWF : cwin A0_FMT_E 4) by (unfold cwin; lia);
    assert (ACC1 : accessible mm A0_FMT_E 4) by (eapply accessible_munch; [exact ACCF| exact MU'| exact CWF| intros s Hs; apply HO; lia]);
    assert (RDF1 : sh_readable mm A0_FMT_E 4) by (eapply sh_readable_munch; [exact RDF| exact MU'| exact CWF| exact HO]);
    pose proof (fmtE_bytes mm MI') as FB1;
    pose proof (icpt_env_stack lo q m mm IE MU' WM' ltac:(lia)) as IE2;
    eapply evt_cut;
    [ eapply pc_int_specq with (lo := lo) (FMT := A0_FMT_E) (fstr := B_E) (pre := []) (b37 := Z_to_bv 8 37) (bc := Z_to_bv 8 100) (post := [Z_to_bv 8 10]);
      [ exact MI' | eassumption | lia | lia | lia | exact (ie_shadow _ IE2) | exact FB1 | exact fmtE_noz | cbn; lia | cbn; lia
      | exact ACC1 | exact RDF1 | reflexivity | constructor | n37_tac | reflexivity | left; reflexivity | discriminate ]
    | post_call asegs mm ] end end.
  clear IE1 IE2 ACC1 RDF1 CF1 CK1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
  pose proof (ie_real_io _ IE1) as (_ & RIO).
  do 5 zstep.
  replace (q + -48) with (q - 48) in * by lia.
  finish. exact FR.
Qed.

Definition vfprintf_front_post0 (q : Z) (gp tp : word) (stream ap : Z) (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (wz VFPRINTF_RESUME) (wz (q - 48)) gp tp t0 t1 t2 (wz A0_FMT_E) (wz stream) (wz stream) (wz A0_FMT_E) (wz ap) a3 a4 a5 a6 a7
                 (wz ap) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz REAL_vfprintf) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q - 48)
    /\ rw_cells asegs m' (q - 48) [C8 (wz ap); C8 (wz ap); C8 s2; C8 s1; C8 s0; C8 ra0].

Lemma vfprintf_front_spec : forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (stream ap lo : Z),
  icpt_env m -> stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 48 - 2400 -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz stream -> a1 = wz A0_FMT_E -> a2 = wz ap ->
  accessible m A0_FMT_E 4 -> sh_readable m A0_FMT_E 4 ->
  evt asegs (vfprintf_front_post0 q gp tp stream ap ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_vfprintf) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros IE ST KLO LO Q64 MI -> -> -> ACCF RDF. unfold A0_vfprintf.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO' : lo <= q - 48) by lia.
  carve_frame 48%nat ST.
  zstep. do 9 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1 end.
  call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
  clear IE1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
  pose proof (ie_cf _ IE1) as CF1. pose proof (ie_ckpf _ IE1) as CK1. unfold env_cf in CF1. unfold env_ckpf in CK1.
  zstep. lit_branch.
  do 4 zstep.
  cbv beta. zsimp. zstep. zstep. lit_branch.
  do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU' : munch [(lo, q)] m mm, WM' : wmono asegs m mm, MI' : mem_inv asegs mm |- _ =>
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia);
    assert (CWF : cwin A0_FMT_E 4) by (unfold cwin; lia);
    assert (ACC1 : accessible mm A0_FMT_E 4) by (eapply accessible_munch; [exact ACCF| exact MU'| exact CWF| intros s Hs; apply HO; lia]);
    assert (RDF1 : sh_readable mm A0_FMT_E 4) by (eapply sh_readable_munch; [exact RDF| exact MU'| exact CWF| exact HO]);
    pose proof (fmtE_bytes mm MI') as FB1;
    pose proof (icpt_env_stack lo q m mm IE MU' WM' ltac:(lia)) as IE2;
    eapply evt_cut;
    [ eapply pc_int_specq with (lo := lo) (FMT := A0_FMT_E) (fstr := B_E) (pre := []) (b37 := Z_to_bv 8 37) (bc := Z_to_bv 8 100) (post := [Z_to_bv 8 10]);
      [ exact MI' | eassumption | lia | lia | lia | exact (ie_shadow _ IE2) | exact FB1 | exact fmtE_noz | cbn; lia | cbn; lia
      | exact ACC1 | exact RDF1 | reflexivity | constructor | n37_tac | reflexivity | left; reflexivity | discriminate ]
    | post_call asegs mm ] end end.
  clear IE1 IE2 ACC1 RDF1 CF1 CK1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
      pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
  pose proof (ie_real_io _ IE1) as (_ & RIO).
  do 6 zstep.
  replace (q + -48) with (q - 48) in * by lia.
  finish.
Qed.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.
Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_pick : forall segs m A pre c post B, rw_cells segs m A (pre ++ c :: post) -> B = A + Z.of_nat (cells_size pre) ->
  rw_cells segs m B [c].
Proof.
  intros segs m A pre c post B H ->. apply rw_cells_app in H. destruct H as [_ H].
  change (c :: post) with ([c] ++ post) in H. apply rw_cells_app in H. exact (proj1 H).
Qed.

Lemma noz_of_notin : forall l : list byte, ~ In (Z_to_bv 8 0) l -> Forall (fun b : byte => bv_unsigned b <> 0) l.
Proof.
  intros l H. apply Forall_forall. intros b Hb E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Definition fprintf_front_post0 (q : Z) (gp tp : word) (stream fmt : Z) (a2 a3 a4 a5 a6 a7 : word) (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' (junk : list byte) (aq : word),
    ms' = MS (mkR (wz FPRINTF_RESUME) (wz (q - 112)) gp tp t0 t1 t2 (wz fmt) (wz stream) (wz stream) (wz fmt) (wz (q - 48)) x13 x14 x15 x16 x17
                 (wz (q - 48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz REAL_vfprintf) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q - 112)
    /\ rw_cells asegs m' (q - 112) [CB 8 junk; C8 (wz (q - 48)); C8 aq; C8 (wz (q - 48)); C8 s2; C8 s1; C8 s0; C8 ra0;
                                  C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

Section FP.
  Variables (FMT : Z) (fstr pre post : list byte) (bc : byte).
  Hypothesis FBY : forall m, mem_inv asegs m -> bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis FL : 1 <= Z.of_nat (length fstr) <= 62.
  Hypothesis FIMG : 0x10000 <= FMT /\ FMT + Z.of_nat (length fstr) + 1 <= 0x609000.
  Hypothesis EF : fstr = pre ++ Z_to_bv 8 37 :: bc :: post.
  Hypothesis NP1 : Forall (fun b : byte => bv_unsigned b <> 37) pre.
  Hypothesis NP2 : Forall (fun b : byte => bv_unsigned b <> 37) post.
  Hypothesis NE : post <> [].
  Notation FN := (Z.of_nat (length fstr) + 1).

  Variables (ra0 : word) (q : Z) (gp tp s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (stream lo : Z).
  Hypothesis IE : icpt_env m.
  Hypothesis ST : stk asegs m lo q.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis LO : lo <= q - 112 - 2400.
  Hypothesis Q64 : q < 2^64.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ACCF : accessible m FMT FN.
  Hypothesis RDF : sh_readable m FMT FN.

  Notation FPOST := (fprintf_front_post0 q gp tp stream FMT a2 a3 a4 a5 a6 a7 ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  #[using="fstr IE ST KLO LO Q64 MI"] Lemma fp_pre : forall t0 t1 t2 a0 a1 t3 t4 t5 t6, a0 = wz stream -> a1 = wz FMT ->
    (forall mm x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 junk,
       munch [(lo, q)] m mm -> wmono asegs m mm -> mem_inv asegs mm -> stk asegs mm lo (q + -112) ->
       rw_cells asegs mm (q + -112) [CB 8 junk; C8 (wz (q + -48)); C8 (wz (q + -48)); C8 (wz (q + -48)); C8 s2; C8 s1; C8 s0; C8 ra0;
                                    C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
       evt asegs FPOST
         (MS (mkR (wz 0x49918) (wz (q + -112)) gp tp x5 x6 x7 (wz FMT) (wz stream) (wz 0x1ee3f) (wz FMT) (wz (q + -48)) x13 x14 x15 x16 x17
                  (wz (q + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (wz 0x48a04) fc None mm (seg_rom asegs))) ->
    evt asegs FPOST
      (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A0_fprintf) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros -> -> K. unfold A0_fprintf.
    pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO' : lo <= q - 112) by lia.
    pose proof ST as ST0. pose proof MI as MI0.
    carve_frame 112%nat ST0.
    zstep. do 15 zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1 end.
    call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
    clear IE1.
    zstep. lit_branch. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
        pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
    call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
    clear IE1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
        pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
    pose proof (ie_cf _ IE1) as CF1. pose proof (ie_ckpf _ IE1) as CK1. unfold env_cf in CF1. unfold env_ckpf in CK1.
    zstep. lit_branch.
    do 4 zstep.
    cbv beta. zsimp. zstep. zstep. lit_branch.
    do 5 zstep.
    eapply K; eassumption.
  Qed.

  #[using="fstr IE KLO"] Lemma fp_post : forall mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 junk,
    munch [(lo, q)] m mm -> wmono asegs m mm -> mem_inv asegs mm -> stk asegs mm lo (q + -112) ->
    rw_cells asegs mm (q + -112) [CB 8 junk; C8 (wz (q + -48)); C8 (wz (q + -48)); C8 (wz (q + -48)); C8 s2; C8 s1; C8 s0; C8 ra0;
                                 C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
    evt asegs FPOST
      (MS (mkR (wz 0x49918) (wz (q + -112)) gp tp x5 x6 x7 (wz FMT) (wz stream) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (q + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x49918) fc None mm (seg_rom asegs)).
  Proof.
    intros until junk. intros MU WM MI1 ST1 FR.
    pose proof (icpt_env_stack lo q m mm IE MU WM ltac:(lia)) as IE1.
    pose proof (ie_real_io _ IE1) as (_ & RIO).
    do 8 zstep.
    replace (q + -112) with (q - 112) in * by lia. replace (q + -48) with (q - 48) in * by lia.
    finish. exact FR.
  Qed.

  #[using="FL FIMG KLO ACCF RDF"] Lemma fp_fmt_facts : forall mm, munch [(lo, q)] m mm -> accessible mm FMT FN /\ sh_readable mm FMT FN.
  Proof.
    intros mm MU.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    assert (CWF : cwin FMT FN) by (unfold cwin; lia).
    split; [eapply accessible_munch; [exact ACCF| exact MU| exact CWF| intros s Hs; apply HO; lia]
           | eapply sh_readable_munch; [exact RDF| exact MU| exact CWF| exact HO]].
  Qed.

  #[using="fstr pre post FBY NOZ FL FIMG EF NP1 NP2 NE IE ST KLO LO Q64 MI ACCF RDF"] Lemma fprintf_int_front : forall t0 t1 t2 a0 a1 t3 t4 t5 t6, intconv (bv_unsigned bc) -> a0 = wz stream -> a1 = wz FMT ->
    evt asegs FPOST
      (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A0_fprintf) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros HC E0 E1. eapply fp_pre; [exact E0| exact E1|].
    intros mm x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 junk MU WM MI1 ST1 FR.
    destruct (fp_fmt_facts mm MU) as (ACC1 & RDF1).
    pose proof (icpt_env_stack lo q m mm IE MU WM ltac:(lia)) as IE2.
    eapply evt_cut;
    [ eapply pc_int_specq with (lo := lo) (FMT := FMT) (fstr := fstr) (pre := pre) (b37 := Z_to_bv 8 37) (bc := bc) (post := post);
      [ exact MI1 | exact ST1 | lia | lia | lia | exact (ie_shadow _ IE2) | exact (FBY mm MI1) | exact NOZ | exact FL | exact FIMG
      | exact ACC1 | exact RDF1 | exact EF | exact NP1 | exact NP2 | reflexivity | exact HC | exact NE ]
    | post_call asegs mm ].
    eapply fp_post; eassumption.
  Qed.

  Variables (Sa : Z) (sbuf : list byte).
  Hypothesis SSTR : bytes_at asegs m Sa (sbuf ++ [Z_to_bv 8 0]).
  Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0) sbuf.
  Notation NS := (Z.of_nat (length sbuf) + 1).
  Hypothesis SEPS : Sa + NS <= lo \/ q <= Sa.
  Hypothesis WINS : cwin Sa NS.
  Hypothesis WIN2S : Sa + NS < 2^47.
  Hypothesis SPOS : 0 < Sa.
  Hypothesis ACCS : accessible m Sa NS.
  Hypothesis RDS : sh_readable m Sa NS.
  Hypothesis NSZ : NS <= 2^43.

  #[using="fstr pre post FBY NOZ FL FIMG EF NP1 NP2 NE IE ST KLO LO Q64 MI ACCF RDF sbuf SSTR SNOZ SEPS WINS WIN2S SPOS ACCS RDS NSZ"] Lemma fprintf_str_front : forall t0 t1 t2 a0 a1 t3 t4 t5 t6, sconv (bv_unsigned bc) -> a0 = wz stream -> a1 = wz FMT -> a2 = wz Sa ->
    evt asegs FPOST
      (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A0_fprintf) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros HC E0 E1 E2. eapply fp_pre; [exact E0| exact E1|].
    intros mm x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 junk MU WM MI1 ST1 FR.
    destruct (fp_fmt_facts mm MU) as (ACC1 & RDF1).
    pose proof (icpt_env_stack lo q m mm IE MU WM ltac:(lia)) as IE2.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    assert (ACS1 : accessible mm Sa NS) by (eapply accessible_munch; [exact ACCS| exact MU| exact WINS| intros s Hs; apply HO; lia]).
    assert (RDS1 : sh_readable mm Sa NS) by (eapply sh_readable_munch; [exact RDS| exact MU| exact WINS| exact HO]).
    assert (SSTR1 : bytes_at asegs mm Sa (sbuf ++ [Z_to_bv 8 0]))
      by (eapply bytes_at_transport; [exact SSTR| exact MU| rewrite length_app; cbn [length disjoint_from]; lia]).
    assert (VAQ : rw_cells asegs mm (q + -48) [C8 (wz Sa)]).
    { rewrite <- E2.
      eapply (rw_cells_pick asegs mm (q + -112) [CB 8 junk; C8 (wz (q + -48)); C8 (wz (q + -48)); C8 (wz (q + -48)); C8 s2; C8 s1; C8 s0; C8 ra0] (C8 a2));
        [exact FR | cbn [cells_size csize Nat.add]; lia]. }
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
    eapply evt_cut;
    [ eapply pc_str_specq with (lo := lo) (FMT := FMT) (fstr := fstr) (pre := pre) (b37 := Z_to_bv 8 37) (bc := bc) (post := post)
                               (AP := q + -48) (Sa := Sa) (sstr := sbuf);
      [ exact MI1 | exact ST1 | lia | lia | lia | exact (ie_shadow _ IE2) | exact (ie_layout _ IE2) | exact (FBY mm MI1) | exact NOZ | exact FL | exact FIMG
      | exact ACC1 | exact RDF1 | exact VAQ | lia | exact SSTR1 | exact SNOZ | lia | exact WINS | exact WIN2S | exact SPOS
      | exact ACS1 | exact RDS1 | exact NSZ | exact EF | exact NP1 | exact NP2 | reflexivity | exact HC | exact NE ]
    | post_call asegs mm ].
    eapply fp_post; eassumption.
  Qed.
End FP.

Ltac n37l_tac :=
  apply Forall_forall; let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
  cbn [firstn skipn B_F1 B_F2 B_F3 B_F4 In] in Hb;
  repeat (destruct Hb as [<-|Hb]; [cbv; discriminate|]); destruct Hb.

Lemma fprintf_u_front_spec : forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (stream lo : Z),
  icpt_env m -> stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 112 - 2400 -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz stream -> a1 = wz A0_FMT_F4 ->
  accessible m A0_FMT_F4 33 -> sh_readable m A0_FMT_F4 33 ->
  evt asegs (fprintf_front_post0 q gp tp stream A0_FMT_F4 a2 a3 a4 a5 a6 a7 ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_fprintf) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros IE ST KLO LO Q64 MI E0 E1 ACCF RDF.
  eapply (fprintf_int_front S_F4 B_F4 (firstn 14 B_F4) (skipn 16 B_F4) (Z_to_bv 8 117));
    first [ exact fmtF4_bytes | exact fmtF4_noz | reflexivity | n37l_tac | discriminate | eassumption | (cbn; lia) | (unfold S_F4; cbn; lia) | (right; reflexivity) | idtac ].
Qed.

Lemma fprintf_s_front_spec : forall (fmt flen : Z), fmt_pct_s fmt flen ->
  forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (stream S lo : Z) (sbuf : list byte),
  icpt_env m -> stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 112 - 2400 -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz stream -> a1 = wz fmt -> a2 = wz S ->
  accessible m fmt flen -> sh_readable m fmt flen ->
  bytes_at asegs m S (sbuf ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sbuf -> 0 < S ->
  (S + (Z.of_nat (length sbuf) + 1) <= lo \/ q <= S) ->
  accessible m S (Z.of_nat (length sbuf) + 1) -> sh_readable m S (Z.of_nat (length sbuf) + 1) ->
  cwin S (Z.of_nat (length sbuf) + 1) -> S + (Z.of_nat (length sbuf) + 1) < 2^47 -> Z.of_nat (length sbuf) + 1 <= 2^43 ->
  evt asegs (fprintf_front_post0 q gp tp stream fmt a2 a3 a4 a5 a6 a7 ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_fprintf) fc None m (seg_rom asegs)).
Proof.
  intros fmt flen HF. intros until sbuf. intros IE ST KLO LO Q64 MI E0 E1 E2 ACCF RDF SSTR NOTIN SPOS SEPS ACCS RDS WINS WIN2 NSZ.
  pose proof (noz_of_notin _ NOTIN) as SNOZ.
  destruct HF as [(-> & ->) | [(-> & ->) | (-> & ->)]].
  - eapply (fprintf_str_front S_F1 B_F1 (firstn 7 B_F1) (skipn 9 B_F1) (Z_to_bv 8 115)) with (Sa := S) (sbuf := sbuf);
      first [ exact fmtF1_bytes | exact fmtF1_noz | reflexivity | n37l_tac | discriminate | eassumption | (cbn; lia) | (unfold S_F1; cbn; lia) | idtac ].
  - eapply (fprintf_str_front S_F2 B_F2 (firstn 17 B_F2) (skipn 19 B_F2) (Z_to_bv 8 115)) with (Sa := S) (sbuf := sbuf);
      first [ exact fmtF2_bytes | exact fmtF2_noz | reflexivity | n37l_tac | discriminate | eassumption | (cbn; lia) | (unfold S_F2; cbn; lia) | idtac ].
  - eapply (fprintf_str_front S_F3 B_F3 (firstn 19 B_F3) (skipn 21 B_F3) (Z_to_bv 8 115)) with (Sa := S) (sbuf := sbuf);
      first [ exact fmtF3_bytes | exact fmtF3_noz | reflexivity | n37l_tac | discriminate | eassumption | (cbn; lia) | (unfold S_F3; cbn; lia) | idtac ].
Qed.
