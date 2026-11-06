(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun XSegAuto EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk16option89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~m93env89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~r44wdenr44went79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~hg29mem_grows79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU9EhX_ubsan~~~~~~hkd4SEGSk14boolm99sym_state89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhPiece5PIECE~~~~~~hq85piecek14andbm96s_knowhq8apc_regions36Stdlib5Lists4Listih37forallb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~ij1arematch_okm94s_pcm96s_regsr46regionr4fregion_flat_chkr4bwent_withinhq85pc_sghq86pc_xknhq86pc_xpchq88pc_xregs46Stdlib6ZArith6BinInt1Ziu43eqbk14prodk13natk15falsehq84pc_kk13nilhq87pc_endshq88pc_entryhq87pc_fuelhq89piece_okXhkd5run_kij15substhq87mkPiecehq85pc_pvij1crematch_fromhq86set_sgk14true37Corelib4Init5Logicjpc2eqjpc3andjpc2exhq8bpiece_checkhq88piece_ok3h5LinuxProcessSemantics5Riscv7Preludejte5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~kgd7FPStateij12Eskgd6fp_csrkgd4mkstkgd7seg_romhf7Z_to_bvm96s_next89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~kod7know_okkod7regs_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXAxSymRun3~~~~~~kuf9env_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~ljc6mstepsr43INVr47outsider4aregions_okhkd9COPY_SPEChkd9FILL_SPEC" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import SA. Import MATCH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PIECE.

Lemma wden_grows : ltac2:(zQ "90!h9!jc!l9!m0!qe!v4!vb!hk0!hod>1E$4>1M>0@1$1@1$0#k0@1$3@1$1@1$0#8>1w@1$2$6@2$7^2@4$5$8^3^2^1").
Proof.
  intros E M w. induction w as [|g r IH]; cbn [wden]; [apply mem_grows_refl|].
  destruct g as [a wd v|db dk sb sk n|db dk n c].
  - eapply mem_grows_trans; [exact IH | apply wbytes_grows].
  - destruct (rdn EhX_ubsan.SEGS (wden EhX_ubsan.SEGS E M r) _ _); [eapply mem_grows_trans; [exact IH | apply wbytes_grows] | exact IH].
  - eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

Record piece := mkPiece {
  pc_k : nat;                       (* [comment removed for export] *)
  pc_fuel : nat;
  pc_ends : list Z;
  pc_entry : sym_state;             (* [comment removed for export] *)
  pc_pv : list nat;                 (* [comment removed for export] *)
  pc_xpc : Z;                       (* [comment removed for export] *)
  pc_xregs : list expr;             (* [comment removed for export] *)
  pc_xkn : list kentry;             (* [comment removed for export] *)
  pc_regions : list region;         (* [comment removed for export] *)
  pc_sg : subst                     (* [comment removed for export] *)
}.

Definition piece_okX : ltac2:(zQ "50!hp5!l9!hpc!vb!huc>1p$4>3ssX$2>2wX@1$1$3$0") := ltac2:(zQ "h30!hv5!hvc!vb!ig5!ii6!l9!in4!io2!io9!hpc!ip2!ipb!iqd!irb!is4!ise!it8!huc!ivc\1p$h1\3ssX$9\2wX@1$5$2@2$0@2$0@2$0@2$h2@1$7^2@1$f^3@5$6@1$h0^3@1$e^3@1$8^2@1$1^2@1$d^3@3$4$2@1$c@1$3^3^1@3$4$a@1$b@1$1^2@1$3^3").
Definition piece_ok : ltac2:(zQ "20!hp5!huc>1p$1$0") := ltac2:(zQ "h00!vb!l9!jg3!hpc!hp5!jga!jh0!m0!jh8!ji0!ji6!jj1!jjd!huc!jk8!jl5\1p$dM5\1x$5$4@1$8^1$6\1n$5M7\1x@1$7@2$2$3@1$1$0$4@5$f@1$8^2@1$c^2@1$a^2@1$b^2@1$9$0\2p0@2$2$3@1$1$0M2\2p0@2$2$3@1$1$0$4^1\3ssX$3\2wX@1$1$0@3$e^5^2^1$6").

(* [comment removed for export] *)
Definition set_sg : ltac2:(zQ "20!huc!jle>1p$0>2sg$1$0") := ltac2:(zQ "c0!jle!jm7!ji6!jj1!jjd!jh8!jn2!ig5!is4!ise!it8!huc\1p$b\2sg$0@a$1@1$5^2@1$4^2@1$2^2@1$3^2@1$6^2@1$9^2@1$a^2@1$8^2@1$7^2^1").
Definition piece_check : ltac2:(zQ "30!hp5!jle!huc>1p$2>5extra>0$1$0$0") := ltac2:(zQ "ha0!hp5!vb!l9!m0!jg3!hpc!jh0!jga!jle!jh8!hv5!ji0!jnb!hvc!io9!ji6!jj1!jjd!jn2!irb!is4!it8!huc!jk8!job!jl5\1p$h6\5extra>0$8$0M7\1x$7$0@1$9^2$6\1n$7M3\1x@1$3@2$4$5@1$2$1$0@5$h9@1$9^3@1$h1^3@1$f^3@1$h0^3@1$b$1\2p0@2$4$5@1$2$1M4\2p0@2$4$5@1$2$1$0^1\3ssX$5\2wX@1$2$1M3\1x@1$3$8$0@6$c@1$h3^6@1$h2^6@1$h5^6@1$h4^6@1$e^2@1$d^2\2sg$8@2$a@3$h7@2$h8^7^1^3^2@1^6^1$6$6").
Lemma piece_check_sound : ltac2:(zQ "a0!hp5!jp5!jr0!jle!jr6!jrd!huc!js3!jt2!job>1p$6>5extra>0$3$0>0@3$2$0@2$7^2^1$1@2$5$3\2sg$3@2$4@3$2$0@1$8@2$9^4^1$1@3$2$0@1^3^1$1").
Proof.
  intros p extra H. unfold piece_check in H. unfold piece_ok.
  destruct (pc_k p) as [|k] eqn:Hk; [discriminate|]. cbn [set_sg pc_k pc_fuel pc_ends pc_entry].
  rewrite Hk.
  destruct (EhX_ubsan.run_k (S k) (pc_fuel p) (pc_ends p) (pc_entry p) []) as [[ssX wX]|]; [|discriminate].
  destruct (rematch_from (pc_sg p) (pc_pv p) (pc_xregs p) (pc_xkn p) (s_regs ssX) (s_know ssX)) as [sg|]; [|discriminate].
  apply andb_true_iff in H as [H1 H2]. exists sg. split; [exact H1 | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem piece_sound : ltac2:(zQ "i71!h9!jc!jr6!hod!m0!jrd!jr0!kg4!qe!kkc!jj1!kl7!kld!km7!kmf!ig5!irb!kna!hp5!ji0!jp5!ko4!io2!kt9!ku4!lif!ln9!lo3!lo9!lp3!vb!hk0!is4!ise!it8!huc!jt2!lq0!lqd&>0@1$1@1$0#k0@1$4@1$1@1$0#8>0$i5>0$i6>1p$i3>2fx$9>1E$8>1R@2$7@1$0#5@1$1@1$0#k0>1M~0>0@3$6$h2@1$i4^5$h4>0@6$hb$3^4@1$a^6@1$h3$he^3^2@2$5$9\3fx'$9@2$5$8\2E'$8@2$5@2$7@1$0#5@1$1@1$0#k0\2R'@2$7@1$0#5@1$1@1$0#k0@2$5~0\2M'~0@2$2@3$h9@1$h5@1$a^b^9^3@2$2@3$ha$3@5$d^a^8@2$h1@1$0#k0@1$h6@1$a^b^7@1$e$3@5$d^4^2@2$h1@1$0#k0@1$i1^b^1@1$e$3@2$2@3$h8@2$b^3@1$h0^b@1$i2^b^2@2$2@4$h7$3@2$b^3@1$h0^b^1@1$i0^b@2$2@2$hd^3@1$f^b@2$2>1a@1$1@1$0#k0>0@3$hc^4@1$f^c^1@3$6@1$4@1$1@1$0#8@1^3^2@1^9^2@2$2@2$hf^7^1@3$6@1$1@1$0#i0@1$c^4@1$c^a").
Proof.
  intros COPY FILL p fx E R M Hok HINV. unfold piece_ok in Hok.
  destruct (pc_k p) as [|k] eqn:Hk; [discriminate|].
  destruct (EhX_ubsan.run_k (S k) (pc_fuel p) (pc_ends p) (pc_entry p) []) as [[ssX wX]|] eqn:Hrun; [|discriminate].
  unfold piece_okX in Hok.
  apply andb_true_iff in Hok as [Hok Hflat]. apply andb_true_iff in Hok as [Hok Hw]. apply andb_true_iff in Hok as [Hpc Hm].
  apply Z.eqb_eq in Hpc.
  ndestruct (EhX_ubsan.run_k_sound COPY FILL k fx (pc_fuel p) (pc_ends p) (pc_entry p) [] ssX wX E R M Hrun HINV)
    as (fx' & E' & R' & Hfc & Hag & Hle & [HR' HK'] & Hcl & Hms).
  destruct (rematch_sound EhX_ubsan.SEGS E' (wden EhX_ubsan.SEGS E' M wX) R' _ _ _ _ _ Hm HR' HK') as [HRT HKT].
  assert (ROK : regions_ok E' (pc_regions p)).
  { unfold regions_ok. apply Forall_forall. intros r Hr. rewrite forallb_forall in Hflat.
    exact (region_flat_chk_sound EhX_ubsan.SEGS E' _ (s_know ssX) r HK' (Hflat r Hr)). }
  exists fx', E', R', (wden EhX_ubsan.SEGS E' M wX).
  split; [exact Hag|]. split; [rewrite <- Hpc; cbn [wden] in Hms; exact Hms|].
  split; [exact HRT|]. split; [exact HKT|]. split; [exact ROK|]. split.
  - intros a Ha. apply (wden_frame EhX_ubsan.SEGS E' M wX (pc_regions p) a Hw (regions_ok_flat _ _ ROK) Ha).
  - split; [apply wden_grows | exact Hfc].
Qed.

End PIECE.
(* [comment removed for export] *)
