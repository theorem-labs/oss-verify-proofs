(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec
  XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun XSegAuto
  EhX_plain EhMatch.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk16option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9EhX_plain~~~~~~m94SEGS89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~qf3env89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~va4wdenva4went79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~hk89mem_growsk14bool89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~hpa5pieceqf9sym_statek14andbhpaapc_regionsqf6s_know36Stdlib5Lists4Listih07forallb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~iiearematch_okhpa5pc_sghpa6pc_xknhpa6pc_xpchpa8pc_xregsqf4s_pcqf6s_regsva6regionvafregion_flat_chkvabwent_within46Stdlib6ZArith6BinInt1Ziu13eqbk14prodk13natk15falsehpa4pc_kk13nilhpa7pc_endshpa8pc_entryhpa7pc_fuelhpa9piece_okXm95run_kiie5substhpa7mkPiecehpa5pc_pviiecrematch_fromhpa6set_sgk14true37Corelib4Init5Logicjp82eqjp83andjp82exhpabpiece_checkhpa8piece_ok3h5LinuxProcessSemantics5Riscv7Preludejta5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~kg97FPStateiie2Eskg96fp_csrkg94mkstkg97seg_romhf7Z_to_bvm99COPY_SPECm99FILL_SPECqf6s_next89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~kq17know_okkq17regs_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXAxSymRun3~~~~~~lg39env_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~ll06mstepsva3INVva7outsidevaaregions_ok" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import SA. Import MATCH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PIECE.

Lemma wden_grows : ltac2:(zQ "90!h9!jc!l9!m0!q8!v4!hja!hk1!ho6>1E$5>1M>0@1$1@1$0#k0@1$3@1$1@1$0#8>1w@1$2$7@2$8^2@4$6$4^3^2^1").
Proof.
  intros E M w. induction w as [|g r IH]; cbn [wden]; [apply mem_grows_refl|].
  destruct g as [a wd v|db dk sb sk n|db dk n c].
  - eapply mem_grows_trans; [exact IH | apply wbytes_grows].
  - destruct (rdn EhX_plain.SEGS (wden EhX_plain.SEGS E M r) _ _); [eapply mem_grows_trans; [exact IH | apply wbytes_grows] | exact IH].
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

Definition piece_okX : ltac2:(zQ "50!hp3!l9!htd!hu6!hk1>1p$2>3ssX$3>2wX@1$1$4$0") := ltac2:(zQ "h30!hv2!hv9!ig7!hk1!ii3!l9!in1!inf!io8!ip2!ipc!htd!iq8!iqf!hu6!ir8!is1!it3!iv9\1p$b\3ssX$e\2wX@1$5$3@2$0@2$0@2$0@2$h2@1$c^2@1$9^3@5$6@1$a^3@1$8^3@1$d^2@1$2^2@1$7^3@3$4$3@1$h1@1$1^3^1@3$4$f@1$h0@1$2^2@1$1^3").
Definition piece_ok : ltac2:(zQ "20!hp3!htd>1p$1$0") := ltac2:(zQ "h00!hk1!l9!jg0!hu6!hp3!jg7!jgd!m0!jh5!jhd!ji3!jie!jja!htd!jk5!jl2\1p$dM5\1x$5$4@1$8^1$6\1n$5M7\1x@1$7@2$2$3@1$1$0$4@5$f@1$8^2@1$c^2@1$a^2@1$b^2@1$9$0\2p0@2$2$3@1$1$0M2\2p0@2$2$3@1$1$0$4^1\3ssX$3\2wX@1$1$0@3$e^5^2^1$6").

(* [comment removed for export] *)
Definition set_sg : ltac2:(zQ "20!htd!jla>1p$0>2sg$1$0") := ltac2:(zQ "c0!jla!jm3!ji3!jie!jja!jh5!jme!hv9!io8!ip2!ipc!htd\1p$b\2sg$0@a$1@1$5^2@1$4^2@1$2^2@1$3^2@1$6^2@1$9^2@1$a^2@1$8^2@1$7^2^1").
Definition piece_check : ltac2:(zQ "30!hp3!jla!htd>1p$2>5extra>0$1$0$0") := ltac2:(zQ "ha0!hp3!hk1!l9!m0!jg0!hu6!jgd!jg7!jla!jh5!hv2!jhd!jn7!ji3!jie!jja!jme!inf!io8!ipc!htd!jk5!jo7!jl2!ig7!iqf\1p$h4\5extra>0$8$0M7\1x$7$0@1$9^2$6\1n$7M3\1x@1$3@2$4$5@1$2$1$0@5$h7@1$9^3@1$f^3@1$d^3@1$e^3@1$b$1\2p0@2$4$5@1$2$1M4\2p0@2$4$5@1$2$1$0^1\3ssX$5\2wX@1$2$1M3\1x@1$3$8$0@6$c@1$h1^6@1$h0^6@1$h3^6@1$h2^6@1$h9^2@1$h8^2\2sg$8@2$a@3$h5@2$h6^7^1^3^2@1^6^1$6$6").
Lemma piece_check_sound : ltac2:(zQ "a0!hp3!jp1!jqc!jla!jr2!jr9!htd!jrf!jse!jo7>1p$6>5extra>0$3$0>0@3$2$0@2$7^2^1$1@2$5$3\2sg$3@2$4@3$2$0@1$8@2$9^4^1$1@3$2$0@1^3^1$1").
Proof.
  intros p extra H. unfold piece_check in H. unfold piece_ok.
  destruct (pc_k p) as [|k] eqn:Hk; [discriminate|]. cbn [set_sg pc_k pc_fuel pc_ends pc_entry].
  rewrite Hk.
  destruct (EhX_plain.run_k (S k) (pc_fuel p) (pc_ends p) (pc_entry p) []) as [[ssX wX]|]; [|discriminate].
  destruct (rematch_from (pc_sg p) (pc_pv p) (pc_xregs p) (pc_xkn p) (s_regs ssX) (s_know ssX)) as [sg|]; [|discriminate].
  apply andb_true_iff in H as [H1 H2]. exists sg. split; [exact H1 | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem piece_sound : ltac2:(zQ "i71!h9!jc!jr2!q8!m0!jr9!jqc!kg0!jie!v4!kk8!kl3!hv9!inf!kl9!km3!kmb!kn6!hp3!jhd!jp1!io8!ip2!ipc!htd!jse!ko0!koc!kp8!iq8!kud!kv8!lk3!lod!lp7!lpd!lq7!hk1!ho6&>0@1$1@1$0#k0@1$4@1$1@1$0#8>0$ha>0$hb>1p$h8>2fx$a>1E$9>1R@2$7@1$0#5@1$1@1$0#k0>1M~0>0@3$6$h2@1$h9^5$h4>0@6$i2$3^4@1$8^6@1$h3$i5^3^2@2$5$a\3fx'$a@2$5$9\2E'$9@2$5@2$7@1$0#5@1$1@1$0#k0\2R'@2$7@1$0#5@1$1@1$0#k0@2$5~0\2M'~0@2$2@3$i0@1$hc@1$8^b^9^3@2$2@3$i1$3@5$f^a^8@2$h1@1$0#k0@1$hd@1$8^b^7@1$h0$3@5$f^4^2@2$h1@1$0#k0@1$h6^b^1@1$h0$3@2$2@3$hf@2$b^3@1$d^b@1$h7^b^2@2$2@4$he$3@2$b^3@1$d^b^1@1$h5^b@2$2@2$i4^3@1$c^b@2$2>1a@1$1@1$0#k0>0@3$i3^4@1$c^c^1@3$6@1$4@1$1@1$0#8@1^3^2@1^9^2@2$2@2$i6^7^1@3$6@1$1@1$0#i0@1$e^4@1$e^a").
Proof.
  intros COPY FILL p fx E R M Hok HINV. unfold piece_ok in Hok.
  destruct (pc_k p) as [|k] eqn:Hk; [discriminate|].
  destruct (EhX_plain.run_k (S k) (pc_fuel p) (pc_ends p) (pc_entry p) []) as [[ssX wX]|] eqn:Hrun; [|discriminate].
  unfold piece_okX in Hok.
  apply andb_true_iff in Hok as [Hok Hflat]. apply andb_true_iff in Hok as [Hok Hw]. apply andb_true_iff in Hok as [Hpc Hm].
  apply Z.eqb_eq in Hpc.
  ndestruct (EhX_plain.run_k_sound COPY FILL k fx (pc_fuel p) (pc_ends p) (pc_entry p) [] ssX wX E R M Hrun HINV)
    as (fx' & E' & R' & Hfc & Hag & Hle & [HR' HK'] & Hcl & Hms).
  destruct (rematch_sound EhX_plain.SEGS E' (wden EhX_plain.SEGS E' M wX) R' _ _ _ _ _ Hm HR' HK') as [HRT HKT].
  assert (ROK : regions_ok E' (pc_regions p)).
  { unfold regions_ok. apply Forall_forall. intros r Hr. rewrite forallb_forall in Hflat.
    exact (region_flat_chk_sound EhX_plain.SEGS E' _ (s_know ssX) r HK' (Hflat r Hr)). }
  exists fx', E', R', (wden EhX_plain.SEGS E' M wX).
  split; [exact Hag|]. split; [rewrite <- Hpc; cbn [wden] in Hms; exact Hms|].
  split; [exact HRT|]. split; [exact HKT|]. split; [exact ROK|]. split.
  - intros a Ha. apply (wden_frame EhX_plain.SEGS E' M wX (pc_regions p) a Hw (regions_ok_flat _ _ ROK) Ha).
  - split; [apply wden_grows | exact Hfc].
Qed.

End PIECE.
(* [comment removed for export] *)
