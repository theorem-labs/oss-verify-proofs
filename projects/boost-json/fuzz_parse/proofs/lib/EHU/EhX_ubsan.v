(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XHoare XFPSteps XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun XSegAuto XSegAuto2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehe7Segment69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~ldfloaded_segments03nat04prod37Corelib7Numbers7BinNumsr01Z04cons04pair37Corelib4Init7Decimalt92D303nilt92D6t92D8t93Nil37Corelib4Init3Nathg9bof_num_uint37Corelib4Init6NumberhiabUIntDecimal37Corelib4Init5Logichke2eq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hm84itab79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XLibSym~~~~~~hr57itab_of79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU9EhX_ubsan~~~~~~hvd2IThvd9IT_RANGEShvd4SEGShm8aitab_soundhm89sym_state89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~in34went06option04true89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XSegAuto23SA2~~~~~~is98seg_autohvd5BFUELhvd7FLD_PCShvd7FMV_PCShvd8FSD1_PCShvd7FSD_PCShvd5X_CPYhvd5X_SET79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~jm07FPState89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib4APSX~~~~~~jqa9copy_spechm85two64jqa9fill_specr04Npos35stdpp9bitvectorbdefinitionskh62bvhke3andhke2ex3h5LinuxProcessSemantics5Riscv7Preludekk65bvmaphm83envhm86s_nexthm84s_pcjm06fp_csrjm04mkstjm07seg_romin33INVin34wdenkh67Z_to_bv04Some04bool37Corelib4Init5Peanokt12le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXAxSymRun3~~~~~~kub9env_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~lj86mstepsin36closedhvd9COPY_SPEChvd9FILL_SPEChvd4runw01Shvd5run_k" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import SR. Import SA2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition SEGS : ltac2:(zQ "20!h8!l3@1$0$1") := ltac2:(zQ "10!p3$0").

Definition IT_RANGES : ltac2:(zQ "40!h8!q5!qa!s9@1$0@2$2$3$1") := ltac2:(zQ "c0!q5!s9!qa!sd!t3!uf!v4!v9!ve!hg3!hhb!hjf@3$3@2$2$1$0@4$4$1$0+knll0N3@3$3@2$2$1$0@4$4$1$0+nrgo8No2@3$3@2$2$1$0@4$4$1$0+pmil4Na@3$3@2$2$1$0@4$4$1$0+pnoo4Nlr6@3$3@2$2$1$0@4$4$1$0+tlvj8@1$a@1$b@1$7@1$8@1$5@1$5$9@3$3@2$2$1$0@4$4$1$0+tttv4Nma@3$3@2$2$1$0@4$4$1$0+vjln8Nhd@1$6@2$2$1$0").
Time Definition IT : itab := Eval vm_compute in XLibSym.itab_of SEGS IT_RANGES.
Lemma IT_eq : ltac2:(zQ "60!hm2!hqd!hv2!ijd!ik3!il0@3$0$1$3@2$2$5$4"). Proof. vm_cast_no_check (@eq_refl itab IT). Qed.   (* [comment removed for export] *)
Lemma IT_ok : ltac2:(zQ "30!il8!ijd!il0@2$0$2$1"). Proof. rewrite IT_eq. apply XLibSym.itab_of_sound. Qed.

Definition X_CPY : Z := 0xee250.          (* [comment removed for export] *)
Definition X_SET : Z := 0xee7d0.          (* [comment removed for export] *)
Definition FSD_PCS : ltac2:(zQ "20!h8!s9@1$0$1") := ltac2:(zQ "30!s9!sd!v4@3$1$0+tspmc@1$2$0"). (* [comment removed for export] *)
Definition FLD_PCS : ltac2:(zQ "20!h8!s9@1$0$1") := ltac2:(zQ "30!s9!sd!v4@3$1$0+tsnuc@1$2$0"). (* [comment removed for export] *)
Definition FSD1_PCS : ltac2:(zQ "20!h8!s9@1$0$1") := ltac2:(zQ "30!s9!sd!v4@3$1$0+toutc@1$2$0"). (* [comment removed for export] *)
Definition FMV_PCS : ltac2:(zQ "20!h8!s9@1$0$1") := ltac2:(zQ "30!s9!sd!v4@3$1$0+tqmv0@1$2$0").  (* [comment removed for export] *)
Definition BFUEL : nat := 64%nat.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition runw : ltac2:(zQ "70!h8!im6!ir3!q5!irb!qa!s9>4fuel$3>4ends@1$0$6>2ss$1>1w@1$0$2@1$4@2$5$1@1$0$2") := ltac2:(zQ "h00!h8!q5!is3!s9!im6!jgc!ir3!jh8!ji1!jic!jj7!jk3!ijd!il0!jke!jl7\4fuel$1\4ends@1$0$3\2ss$4\1w@1$0$6@e$5$d$c$e$f$b$8$a$9$7^4$2^3^2^1").
Fixpoint run_k (k fuel : nat) (ends : list Z) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  match k with
  | O => Some (ss, w)
  | S k' => match runw fuel ends ss w with Some (ss', w') => run_k k' fuel ends ss' w' | None => None end
  end.

(* [comment removed for export] *)
Definition COPY_SPEC : ltac2:(zQ "00P") := ltac2:(zQ "40!jpf!juc!il0!jke>2fx$0@3$1^1$2$3").
Definition FILL_SPEC : ltac2:(zQ "00P") := ltac2:(zQ "50!jv9!jpf!kg2!il0!jl7>2fx$1@4$2^1$3$4$0").

Theorem runw_sound : ltac2:(zQ "i30!kgf!il0!h8!kj3!kj9!im6!ir3!hm2!kk0!kmc!kn5!knc!jpf!irb!qa!ko6!koe!kp8!kq0!kqb!kr2!kra!ks5!ksb!q5!t3!is3!ku5!s9!lib!ln5!lnf!lo9!lp6!lq3>0$i0>0$i1>2fx$c>4fuel$h8>4ends@1$2$hc>2ss$5>1w@1$2$6>3ss'$5>2w'@1$2$6>1E$a>1R@2$9@1$0#5@1$3@1$0#k0>1M>0@1$3@1$0#k0@1$d@1$3@1$0#8>0@3$7@1$d@2$e$5@1$2$6@4$i2^9^8^7^6@2$h6@2$e$5@1$2$6@4$h9$5@1$2$6^5^4>0@6$h3$1^4^8^7^3^2@2$8$c\3fx'$c@2$8$a\2E'$a@2$8@2$9@1$0#5@1$3@1$0#k0\2R'@2$9@1$0#5@1$3@1$0#k0@2$4@3$7@1$3@1$0#i0@1$h0^3@1$h0^f@2$4@3$hd@1$b^c^8^2@2$4@2$hb@1$b^c@1$b^a@2$4@6$h3$1^2^a^9^1^6@2$4@3$7$h7@2$hf^a^9$ha@3$he$1@5$h1^f^7@2$h5@1$0#k0@1$f^c@4$h4$1^8^6^b@1$h2$1@5$h1^3^1@2$h5@1$0#k0@1$f^a@4$h4$1^2^6^9@1$h2$1").
Proof.
  intros COPY FILL fx fuel ends ss w ss' w' E R M Hrun HINV.
  exact (seg_auto_sound SEGS IT X_CPY X_SET FSD_PCS FLD_PCS FSD1_PCS FMV_PCS BFUEL IT_ok COPY FILL fx fuel true ends ss w ss' w' E R M Hrun HINV).
Qed.

Theorem run_k_sound : ltac2:(zQ "i40!kgf!il0!h8!kj3!kj9!im6!ir3!hm2!kk0!kmc!kn5!knc!jpf!q5!irb!qa!ko6!koe!kp8!kq0!kqb!kr2!kra!lqb!ks5!ksb!t3!is3!ku5!s9!lib!ln5!lnf!lo9!lp6!lqe>0$i1>0$i2>1k$d>2fx$c>4fuel$d>4ends@1$2$hd>2ss$5>1w@1$2$6>3ss'$5>2w'@1$2$6>1E$a>1R@2$9@1$0#5@1$3@1$0#k0>1M>0@1$3@1$0#k0@1$e@1$3@1$0#8>0@3$7@1$e@2$f$5@1$2$6@5$i3@1$h7^b^9^8^7^6@2$h8@2$f$5@1$2$6@4$ha$5@1$2$6^5^4>0@6$h4$1^4^8^7^3^2@2$8$c\3fx'$c@2$8$a\2E'$a@2$8@2$9@1$0#5@1$3@1$0#k0\2R'@2$9@1$0#5@1$3@1$0#k0@2$4@3$7@1$3@1$0#i0@1$h1^3@1$h1^f@2$4@3$he@1$b^c^8^2@2$4@2$hc@1$b^c@1$b^a@2$4@6$h4$1^2^a^9^1^6@2$4@3$7$h9@2$i0^a^9$hb@3$hf$1@5$h2^f^7@2$h6@1$0#k0@1$h0^c@4$h5$1^8^6^b@1$h3$1@5$h2^3^1@2$h6@1$0#k0@1$h0^a@4$h5$1^2^6^9@1$h3$1").
Proof.
  intros COPY FILL k. induction k as [|k IH]; intros fx fuel ends ss w ss' w' E R M Hrun HINV.
  - cbn [run_k] in Hrun. destruct (runw fuel ends ss w) as [[ss1 w1]|] eqn:H1; [|discriminate].
    injection Hrun as <- <-. eapply runw_sound; eauto.
  - cbn [run_k] in Hrun. destruct (runw fuel ends ss w) as [[ss1 w1]|] eqn:H1; [|discriminate].
    ndestruct (runw_sound COPY FILL fx fuel ends ss w ss1 w1 E R M H1 HINV) as (fx1 & E1 & R1 & Hfc1 & Hag1 & Hle1 & HINV1 & Hc1 & Hms1).
    change (run_k (S k) fuel ends ss1 w1 = Some (ss', w')) in Hrun.
    ndestruct (IH fx1 fuel ends ss1 w1 ss' w' E1 R1 M Hrun HINV1) as (fx' & E' & R' & Hfc2 & Hag2 & Hle2 & HINV' & Hc' & Hms2).
    nexists fx', E', R'. split; [rewrite Hfc2; exact Hfc1|]. split.
    { eapply XSegLib.APS.env_agree_trans; [exact Hag1|]. eapply XSegLib.APS.env_agree_le; [exact Hag2 | exact Hle1]. }
    split; [lia|]. split; [exact HINV'|]. split; [exact Hc'|]. eapply msteps_trans; [exact Hms1 | exact Hms2].
Qed.
(* [comment removed for export] *)
