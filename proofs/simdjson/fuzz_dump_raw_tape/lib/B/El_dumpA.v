(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_state RT_rep RT_stackmalloc RT_stackmalloc1 RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_contracts2 RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec RT_drain_rhead RT_freeP RT_smgc RT_artfacts TopA_iodefs RT_io RT_cli RT_iclifts RT_np R_isPoisoned F_achk El_defsA El_os_defsA El_ins_ifaceA El_esc_ifaceA El_os_putA El_os_insLA El_os_insdLA El_os_insiLA El_setfillA El_escA El_dump_topA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.

Definition el_RC2 : rt_contracts2 RTA :=
  rta_contracts2 (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
    (rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok))
    smgc_proof smgc1_proof.
Definition el_RC : rt_contracts RTA := rc2_rt RTA el_RC2.

Lemma el_dccA_rta : forall Σ m, ART RTA Σ m -> el_dccA m.
Proof.
  intros Σ m H. pose proof (rta_cli_ro Σ m H) as C. unfold el_dccA.
  repeat split; (eapply (cli_ro_at m _ _ C); cli_in).
Qed.

Lemma el_ictx_rta : forall Σ m, ART RTA Σ m -> ictx m.
Proof. intros Σ m H. pose proof (rta_ic Σ m H) as (IC1 & IC2 & _ & IC4 & IC5). unfold ictx. split; [exact IC1|]. split; [exact IC2|]. split; [exact IC4| exact IC5]. Qed.

Local Ltac plug := first
  [ exact rta_art_facts | exact el_RC | exact el_RC2 | exact rip_proof | exact el_ictx_rta | exact rta_shw | exact el_dccA_rta | exact rta_np | assumption ].

Lemma el_dump : forall PMc, dump_cpsA RTA PMc.
Proof.
  intros PMc. apply (dump_okA2 RTA rta_art_facts el_RC el_RC2 PMc); intros FDO MST.
  - eapply put_okXA; plug.
  - eapply ins_ul_okA; plug.
  - eapply ins_u_okA; plug.
  - eapply ins_l_okA; plug.
  - eapply ins_d_okA; plug.
  - eapply esc_okA; try plug.
    + eapply put_okXA; plug.
    + eapply setfill_okA; plug.
    + eapply ins_i_okA; plug.
Qed.
