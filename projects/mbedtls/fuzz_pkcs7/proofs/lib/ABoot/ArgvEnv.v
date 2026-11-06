(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec SeqExec StepTac.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ArgvEnv () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Scaffold.wmem"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.stack_to_mem"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_image"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.ABoot.CatExec.cat_argv_ptr"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Lists.ListDef.nth"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv_add"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.nat_to_word"; "Corelib.Init.Nat.add"; "Corelib.Init.Nat.mul"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_le8"].


Section Scaffold.

  (* [comment removed for export] *)
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Variable ph : PhdrInfo.

  Variable sp : word.
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.

  (* [comment removed for export] *)
  Variable rnd : EntryDraw.

  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hsp_lo"] Lemma sp_lo_num : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. exact Hsp_lo. Qed.

  #[using="Hsp_hi"] Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. exact Hsp_hi. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition argcN : word := len_word av.

  #[using="Hva"] Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
  Proof.
    pose proof (valid_argv_len av Hva).
    unfold argcN, len_word. apply u_Z2bv; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hva Hve Hsp_hi"] Lemma bsb_nw :
    (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z.
  Proof.
    pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof sp_hi_num. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition envp_ptr : word :=
    Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length av) + 8).

  #[using="Hva Hsp_lo Hsp_hi"] Lemma envp_ptr_eq :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned sp + 8)) (v_slli argcN 3)) 8 = envp_ptr.
  Proof.
    pose proof sp_hi_num. pose proof sp_lo_num.
    pose proof (valid_argv_len av Hva) as Hlen.
    apply bv_eq. unfold envp_ptr, v_addi.
    rewrite !Z_to_bv_unsigned.
    rewrite v_add_small
      by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
          rewrite u_argcN; lia).
    rewrite u_Z2bv by lia.
    rewrite v_slli_3 by (rewrite u_argcN; lia).
    rewrite u_argcN.
    f_equal; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition wmem : word -> option byte := wrap_mem ph sp av ev uid hw rnd.

  (* [comment removed for export] *)
  #[using="Type"] Lemma rdn_wmem_stack : ltac2:(CDefT.buildp (gd_tbl_ArgvEnv ()) "Pa,(0.&40.)Pn,$1.P,(2.(3.&40.Vsp,)(3.&40.R2.))P,(2.(4.(3.&40.R3.)(5.R2.))(6.+2.+40.))(7.(8.(9.(0.&8.)))(:.Vsegs,$;.R4.R3.)(:.Vsegs,(<.Vsp,(=.Vph,Vsp,Vav,Vev,Vuid,Vhw,Vrnd,))R4.R3.))")
(* [comment removed for export] *).
  Proof. intros a n Ha Hn. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi"] Lemma read_argc_w :
    rdn segs wmem sp 8%nat = Some (word_le8 argcN).
  Proof.
    pose proof sp_hi_num.
    rewrite rdn_wmem_stack by lia.
    apply read_argc. exact bsb_nw.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi"] Lemma argv_ptr_bounds_at : ltac2:(CDefT.buildp (gd_tbl_ArgvEnv ()) "Pk,$1.P,(>.R1.(?.(9.(0.&8.))Vav,))(10.(2.(3.&40.Vsp,)(3.&40.(11.Vsp,Vav,Vev,R2.)))(12.(4.(4.(3.&40.(11.Vsp,Vav,Vev,R2.))(5.(?.(0.&8.)(13.(9.(0.&8.))R2.Vav,(14.(0.&8.))))))+1.)(6.+2.+40.)))")
(* [comment removed for export] *).
  Proof.
    intros k Hk. apply argv_ptr_bounds; try assumption.
    pose proof sp_hi_num. unfold argv_layout_slack. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_lo Hsp_hi"] Lemma read_argv_ptr_w : ltac2:(CDefT.buildp (gd_tbl_ArgvEnv ()) "Pk,$1.P,(>.R1.(?.(9.(0.&8.))Vav,))(7.(8.(9.(0.&8.)))(:.Vsegs,$;.(15.&40.Vsp,(16.(17.#8.(18.#8.R2.))))#8.)(19.(9.(0.&8.))(1:.(11.Vsp,Vav,Vev,R2.))))")
(* [comment removed for export] *).
  Proof.
    intros k Hk. pose proof sp_lo_num. pose proof sp_hi_num.
    pose proof (valid_argv_len av Hva) as Hal.
    rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
    apply read_argv_ptr_k; [ exact Hk | exact bsb_nw ].
  Qed.

End Scaffold.
