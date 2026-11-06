(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseRdKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RF_fse_iface.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Record rdctx : Type := mkRD {
  c_ra : word; c_gp : word; c_tp : word;
  c_s0 : word; c_s1 : word; c_s2 : word; c_s3 : word; c_s4 : word; c_s5 : word; c_s6 : word;
  c_s7 : word; c_s8 : word; c_s9 : word; c_s10 : word; c_s11 : word;
  c_F : bvmap 5 word; c_fc : bv 32;
  c_m : fmem;                               (* [comment removed for export] *)
  c_SP : Z; c_NC : Z; c_MSVP : Z; c_TLP : Z; c_BUF : Z; c_lo : Z;
  c_rt0 : list Z; c_buf : list Z; c_msv0 : Z
}.

Definition RD_STACK : Z := 112.

Definition rd_W (C : rdctx) : list (Z * Z) :=
  [(c_NC C, c_NC C + 2 * zlen (c_rt0 C)); (c_MSVP C, c_MSVP C + 4); (c_TLP C, c_TLP C + 4); (c_SP C - RD_STACK, c_SP C)].

(* [comment removed for export] *)
Definition rd_ok (C : rdctx) : Prop :=
  8 <= zlen (c_buf C) <= 1048576 /\ Forall (fun c => 0 <= c < 256) (c_buf C)
  /\ 0 <= c_msv0 C <= 255 /\ c_msv0 C + 1 <= zlen (c_rt0 C)
  /\ 0 <= c_SP C < 2^64 /\ c_lo C <= c_SP C - RD_STACK /\ 0 <= c_lo C
  /\ (0 <= c_NC C /\ c_NC C + 2 * zlen (c_rt0 C) <= 2^64) /\ (0 <= c_BUF C /\ c_BUF C + zlen (c_buf C) + 8 <= 2^64)
  /\ (0 <= c_MSVP C /\ c_MSVP C + 4 <= 2^64) /\ (0 <= c_TLP C /\ c_TLP C + 4 <= 2^64)
  /\ (c_NC C + 2 * zlen (c_rt0 C) <= c_lo C \/ c_SP C <= c_NC C)      (* [comment removed for export] *)
  /\ (c_MSVP C + 4 <= c_lo C \/ c_SP C <= c_MSVP C)
  /\ (c_TLP C + 4 <= c_lo C \/ c_SP C <= c_TLP C)
  /\ (c_BUF C + zlen (c_buf C) <= c_lo C \/ c_SP C <= c_BUF C)
  /\ (c_NC C + 2 * zlen (c_rt0 C) <= c_MSVP C \/ c_MSVP C + 4 <= c_NC C)
  /\ (c_NC C + 2 * zlen (c_rt0 C) <= c_TLP C \/ c_TLP C + 4 <= c_NC C)
  /\ (c_NC C + 2 * zlen (c_rt0 C) <= c_BUF C \/ c_BUF C + zlen (c_buf C) <= c_NC C)
  /\ (c_MSVP C + 4 <= c_TLP C \/ c_TLP C + 4 <= c_MSVP C)
  /\ (c_MSVP C + 4 <= c_BUF C \/ c_BUF C + zlen (c_buf C) <= c_MSVP C)
  /\ (c_TLP C + 4 <= c_BUF C \/ c_BUF C + zlen (c_buf C) <= c_TLP C).

(* [comment removed for export] *)
Definition rd_inv (C : rdctx) (m1 : fmem) (nc : list Z) (msvw tlw : word) : Prop :=
  u8arr psegs m1 (c_NC C) (u16s (map (Z_to_bv 64) nc)) /\ length nc = length (c_rt0 C)
  /\ bytes_at psegs m1 (c_BUF C) (map (Z_to_bv 8) (c_buf C))
  /\ rw_cells psegs m1 (c_MSVP C) [C4 msvw]
  /\ rw_cells psegs m1 (c_TLP C) [C4 tlw]
  /\ (exists junk8, rw_cells psegs m1 (c_SP C + -112)
        [CB 8 junk8; C8 (c_s11 C); C8 (c_s10 C); C8 (c_s9 C); C8 (c_s8 C); C8 (c_s7 C); C8 (c_s6 C); C8 (c_s5 C);
         C8 (c_s4 C); C8 (c_s3 C); C8 (c_s2 C); C8 (c_s1 C); C8 (c_s0 C); C8 (c_ra C)])
  /\ stk psegs m1 (c_lo C) (c_SP C + -112)
  /\ munch (rd_W C) (c_m C) m1 /\ wmono psegs (c_m C) m1 /\ mem_inv psegs m1.

(* [comment removed for export] *)
Definition rd_body_post (C : rdctx) (rt : list Z) (msv tl n : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (c_ra C) (Z_to_bv 64 (c_SP C)) (c_gp C) (c_tp C) t0 t1 t2 (c_s0 C) (c_s1 C) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                 (c_s2 C) (c_s3 C) (c_s4 C) (c_s5 C) (c_s6 C) (c_s7 C) (c_s8 C) (c_s9 C) (c_s10 C) (c_s11 C) t3 t4 t5 t6)
             (c_F C) (ret_pc (c_ra C)) (c_fc C) None m' (seg_rom psegs)
    /\ munch (rd_W C) (c_m C) m'
    /\ wmono psegs (c_m C) m' /\ mem_inv psegs m'
    /\ stk psegs m' (c_lo C) (c_SP C)
    /\ u8arr psegs m' (c_NC C) (u16s (map (Z_to_bv 64) rt))
    /\ rw_cells psegs m' (c_MSVP C) [C4 (Z_to_bv 64 msv)]
    /\ rw_cells psegs m' (c_TLP C) [C4 (Z_to_bv 64 tl)].

(* [comment removed for export] *)
Definition rd_lst (C : rdctx) (pc : Z) (m1 : fmem) (x1 x12 x14 x20 x22 x23 x24 x25 x26 x27 x30 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (c_SP C + -112)) (c_gp C) (c_tp C)
          (Z_to_bv 64 (c_BUF C + zlen (c_buf C) + -7)) (Z_to_bv 64 (c_BUF C + zlen (c_buf C) + -4)) (Z_to_bv 64 1431655765)
          (Z_to_bv 64 (c_MSVP C)) (Z_to_bv 64 (c_BUF C)) (Z_to_bv 64 32) (Z_to_bv 64 1) x12 (Z_to_bv 64 2) x14
          (Z_to_bv 64 18446744071562067968) (Z_to_bv 64 24) (Z_to_bv 64 23)
          (Z_to_bv 64 (c_NC C)) (Z_to_bv 64 125613361) x20 (Z_to_bv 64 (c_msv0 C + 1)) x22 x23 x24 x25 x26 x27
          (Z_to_bv 64 858993459) (Z_to_bv 64 252645135) x30 (Z_to_bv 64 16843009))
     (c_F C) (Z_to_bv 64 pc) (c_fc C) None m1 (seg_rom psegs).

(* [comment removed for export] *)
Definition rd_head (C : rdctx) (s : rstate) (m1 : fmem) (x1 x25 x26 x27 : word) : machine_state :=
  rd_lst C (if r_previous0 s then 0x249f4 else 0x249ec) m1 x1 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (c_BUF C + r_ip s))
         (Z_to_bv 64 (r_threshold s)) (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_charnum s))
         (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) x25 x26 x27 (Z_to_bv 64 (r_nbBits s)).

(* [comment removed for export] *)
Definition rd_cnt (C : rdctx) (s : rstate) (m1 : fmem) (x1 x23 x26 x27 : word) : machine_state :=
  rd_lst C 0x24b00 m1 x1 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (c_BUF C + r_ip s))
         (Z_to_bv 64 (r_threshold s)) (Z_to_bv 64 (r_bitCount s)) x23
         (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) (Z_to_bv 64 (r_charnum s)) x26 x27 (Z_to_bv 64 (r_nbBits s)).

(* [comment removed for export] *)
Definition rd_exit (C : rdctx) (s : rstate) (m1 : fmem) (x1 x20 x23 x24 x26 x27 x30 : word) : machine_state :=
  rd_lst C 0x24c80 m1 x1 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (c_BUF C + r_ip s)) x20 (Z_to_bv 64 (r_bitCount s)) x23 x24
         (Z_to_bv 64 (r_charnum s)) x26 x27 x30.

(* [comment removed for export] *)
Definition rd_brk_ok (C : rdctx) (s : rstate) : Prop :=
  0 <= r_remaining s < 2^31 /\ 0 <= r_bitCount s < 2^31 /\ 0 <= r_charnum s < 2^31 /\ 0 <= r_ip s /\ r_ip s + 4 <= zlen (c_buf C).

Section Base.
  Variable C : rdctx.
  Hypothesis OK : rd_ok C.

  (* [comment removed for export] *)
  Lemma buf_rd : forall m1 i, bytes_at psegs m1 (c_BUF C) (map (Z_to_bv 8) (c_buf C)) -> 0 <= i < zlen (c_buf C) ->
    ov_read_bytes psegs m1 (Z_to_bv 64 (c_BUF C + i)) 1 = Some [Z_to_bv 8 (Znth i (c_buf C))] /\ 0 <= Znth i (c_buf C) < 256.
  Proof.
    intros m1 i HB Hi. destruct OK as (_ & FB & _). unfold Znth.
    assert (L : (Z.to_nat i < length (c_buf C))%nat) by lia.
    split.
    - eapply (u8ro_read psegs m1 (c_BUF C) _ i); [exact HB| | lia| unfold wa; f_equal; lia].
      rewrite nth_error_map. rewrite (nth_error_nth' (c_buf C) 0 L). reflexivity.
    - apply (proj1 (Forall_forall _ _) FB). apply nth_In. exact L.
  Qed.

  Lemma buf_all_bytes : all_bytes (c_buf C).
  Proof. destruct OK as (_ & FB & _). apply Forall_all_bytes. exact FB. Qed.
End Base.
