(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Abbreviation f5_pins := [(2%bv : reg, ZV 32); (10%bv : reg, ZV 33)].
(* [comment removed for export] *)
Abbreviation f5_uvi_hi :=
  [Some (0x10007fff8000 + 16, 0x800000000000); Some (0x10007fff8000, 0x800000000000 - 2048);
   Some (0x688000, 0x800000000000 - 1)].
Abbreviation f5_uvi_lo :=
  [Some (0x10007fff8000 + 16, 0x800000000000); Some (0x688000, 0x7fff7000 - 2048);
   Some (0x688000, 0x800000000000 - 1)].
Abbreviation f5_kn :=
  [KC (ZV 33) 2040 8 (ZV 34);
   KC (ZL 0) 0x129ea8 8 (ZL 0x132278); KC (ZL 0) 0x132278 8 (ZL 0x7fff8000);
   KC (ZL 0) 0x129eb0 8 (ZL 0x132f68); KC (ZL 0) 0x129eb8 8 (ZL 0x132f70);
   KC (ZL 0) 0x132f68 8 (ZL 0); KC (ZL 0) 0x132f70 8 (ZL 0);
   KC (ZL 0) 0x129ec0 8 (ZL 0x132f60); KC (ZL 0) 0x132f60 8 (ZL 0x7fffffffffff);
   KC (ZL 0) 0x10380 8 (ZL 0xf5f5f5f5f5f5f5f5)].
Abbreviation f5_kw := [KW (ZV 32) (-16) 0; KW (ZV 34) 0 1; KW (ZDivP (ZV 33) 3) 0x7fff8000 (0x7fff8000 + 256)].
Abbreviation f5_ctx uvi := (CTX (vi_regs ++ uvi) f5_kn f5_kw).

(* [comment removed for export] *)
Lemma f5_bytes : forall j, 0 <= j < 8 ->
  (bv_unsigned (Z_to_bv 64 17723342345328784885) / 2 ^ (8 * j)) mod 256 = 0xf5 mod 256.
Proof.
  intros j Hj. rewrite u_Z2bv64.
  assert (X : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
  destruct X as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fill_step : forall M base (K n : Z) a (w : word) c,
  n = 8 * K + 8 -> a = base + 8 * K -> 0 <= K -> 0 <= base -> base + n <= 2 ^ 64 ->
  (forall j, 0 <= j < 8 -> (bv_unsigned w / 2 ^ (8 * j)) mod 256 = c mod 256) ->
  (forall t, 0 <= t < 8 * K -> mem_byte M (base + t) c) ->
  forall t, 0 <= t < n -> mem_byte (wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 w)) (base + t) c.
Proof.
  intros M base K n a w c -> -> HK Hb Hhi Hw HM t Ht.
  destruct (Z.lt_ge_cases t (8 * K)) as [Hlt|Hge].
  - apply mem_byte_wb_out; try (change (Z.of_nat 8) with 8); try lia. apply HM. lia.
  - apply mem_byte_wb_in; try (change (Z.of_nat 8) with 8); try lia. apply Hw. lia.
Qed.

Ltac fill_go :=
  lazymatch goal with
  | |- forall t, 0 <= t < ?n -> mem_byte _ _ _ =>
      first
        [ let k := eval vm_compute in (n / 8 - 1) in
          let k8 := eval vm_compute in (8 * k) in
          eapply (fill_step _ _ k); [reflexivity | lia | lia | lia | lia | exact f5_bytes |];
          change (8 * k) with k8; fill_go
        | intros ? ?; exfalso; lia ]
  end.

(* [comment removed for export] *)
Ltac land_lit :=
  repeat match goal with
  | |- context [Z.land ?a ?b] => let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  end.

Theorem free5_A : free5_stmt.
Proof.
  unfold free5_stmt.
  intros fx regs mem rom ret sp f q R1 Hret R2 Hsp16 Hsplo Hsphi Hdsp R10 Hf8 Hflo Hfapp Hfhi Hq Hqlo Hqapp Hqhi Hdq Hdsh
         D1 D2 D3 D4 D5 Hrt Hro.   (* [comment removed for export] *)
  unfold app_mem in *. unfold KHI_A, HIEND_A, IMGHI_A, LOSH_A, FREE5_FR, FREE5_A, sh, SH_A, w64 in *.
  replace (Z_to_bv 5 1) with (1%bv : reg) in R1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 2) with (2%bv : reg) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 10) with (10%bv : reg) in R10 by (apply bv_eq; reflexivity).
  pose proof (ret_ok_of_mod4 ret Hret) as Hret'.
  hide D1; hide D2; hide D3; hide D4; hide D5; hide Hsp16; hide Hf8; hide Hret.
  (* [comment removed for export] *)
  assert (Cq : cellN SEGS_A mem (f + 2040) 8 q) by (apply cellN_u64'; [exact Hq|lia|lia|lia]).
  assert (C1 : cellN SEGS_A mem 0x129ea8 8 0x132278) by (apply (cellN_ro_A mem); [exact Hro|vm_compute; reflexivity|vm_compute; reflexivity|lia|cbn; lia]).
  assert (C2 : cellN SEGS_A mem 0x132278 8 0x7fff8000) by (apply (cellN_rt_A mem); [exact Hrt|vm_compute; reflexivity|lia|cbn; lia]).
  assert (C3 : cellN SEGS_A mem 0x129eb0 8 0x132f68) by (apply (cellN_ro_A mem); [exact Hro|vm_compute; reflexivity|vm_compute; reflexivity|lia|cbn; lia]).
  assert (C4 : cellN SEGS_A mem 0x129eb8 8 0x132f70) by (apply (cellN_ro_A mem); [exact Hro|vm_compute; reflexivity|vm_compute; reflexivity|lia|cbn; lia]).
  assert (C5 : cellN SEGS_A mem 0x132f68 8 0) by (apply (cellN_rt_A mem); [exact Hrt|vm_compute; reflexivity|lia|cbn; lia]).
  assert (C6 : cellN SEGS_A mem 0x132f70 8 0) by (apply (cellN_rt_A mem); [exact Hrt|vm_compute; reflexivity|lia|cbn; lia]).
  assert (C7 : cellN SEGS_A mem 0x129ec0 8 0x132f60) by (apply (cellN_ro_A mem); [exact Hro|vm_compute; reflexivity|vm_compute; reflexivity|lia|cbn; lia]).
  assert (C8 : cellN SEGS_A mem 0x132f60 8 0x7fffffffffff) by (apply (cellN_rt_A mem); [exact Hrt|vm_compute; reflexivity|lia|cbn; lia]).
  assert (C9 : cellN SEGS_A mem 0x10380 8 0xf5f5f5f5f5f5f5f5) by (apply (cellN_ro_A mem); [exact Hro|vm_compute; reflexivity|vm_compute; reflexivity|lia|cbn; lia]).
  (* [comment removed for export] *)
  assert (Wsp : RiscvSemantics.store_ok SEGS_A mem (Z_to_bv 64 (sp - 16)) 16 = true).
  { change 16%nat with (Z.to_nat 16). apply store_ok_of_def; [exact Hdsp|lia|lia|lia]. }
  assert (Wq : RiscvSemantics.store_ok SEGS_A mem (Z_to_bv 64 q) 1 = true).
  { change 1%nat with (Z.to_nat 1). apply store_ok_of_def; [exact Hdq|lia|lia|lia]. }
  assert (Wsh : RiscvSemantics.store_ok SEGS_A mem (Z_to_bv 64 (2147450880 + f / 8)) 256 = true).
  { change 256%nat with (Z.to_nat 256). apply store_ok_of_def; [exact Hdsh|lia|lia|lia]. }
  (* [comment removed for export] *)
  destruct Hfapp as [HfL | HfH];
    [ zx_run SEGS_A constr:(f5_ctx f5_uvi_lo) 120%nat (@nil Z) (SCR [false] []) constr:(f5_pins) [sp; f; q] constr:(f5_uvi_lo) regs mem rom 0x5b8ac
    | zx_run SEGS_A constr:(f5_ctx f5_uvi_hi) 120%nat (@nil Z) (SCR [false] []) constr:(f5_pins) [sp; f; q] constr:(f5_uvi_hi) regs mem rom 0x5b8ac ].
  all: zx_use ZXB
    ltac:(zx_pins)
    ltac:(zx_lia)
    ltac:(kc1 Cq; kc1 C1; kc1 C2; kc1 C3; kc1 C4; kc1 C5; kc1 C6; kc1 C7; kc1 C8; kc1 C9; exact I)
    ltac:(kw1 Wsp; kw1 Wq; kw1 Wsh; exact I)
    ltac:(unhide; zx_scs ltac:(land_lit; lia)).
  all: unhide.
  all: clear ZF.
  all: assert (R1' : getr regs0 1%bv = ret) by (rewrite <- R1; eapply reg_kept; [exact ZR|reflexivity]).
  all: eexists regs0, _; split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret']|].
  all: clear ZM.
  all: split; [apply keeps_cs_of_keeps; eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
  all: clear ZE ZR R1' Cq C1 C2 C3 C4 C5 C6 C7 C8 C9 Wsp Wq Wsh.
  all: split; [|split];
  [ (* [comment removed for export] *)
    clear D1 D2 D3 D5;
    do 32 (apply mem_byte_wb_out; [lia | change (Z.of_nat 8) with 8; lia | lia | change (Z.of_nat 8) with 8; lia |]);
    apply mem_byte_wb_in; [lia | change (Z.of_nat 1) with 1; lia | change (Z.of_nat 1) with 1; lia |];
    rewrite u_Z2bv64, Z.sub_diag; reflexivity
  | (* [comment removed for export] *)
    clear D1 D2 D3 D4 D5;
    fill_go
  | (* [comment removed for export] *)
    clear D1 D2 D3 D4 D5;
    apply mem_frame_of_unch; [unchx | growsx] ].
Qed.
