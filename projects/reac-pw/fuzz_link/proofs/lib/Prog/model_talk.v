(* reac-pw/fuzz_link, PLAIN build: model_read and model_write with talk's walk (lib/Prog/talk.v)
   filled in. index_of_contract_P is the one callee contract left; its walk is another lane's. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  index_of_c model_read_c model_write_c model_read model_write talk.

Theorem model_read_holds_talk : index_of_contract_P -> model_read_contract.
Proof. intros HI. exact (model_read_holds_closed HI talk_holds). Qed.

Theorem model_write_holds_talk : index_of_contract_P -> model_write_contract.
Proof. intros HI. exact (model_write_holds_closed HI talk_holds). Qed.

About model_read_holds_talk.
About model_write_holds_talk.
Print Assumptions model_read_holds_talk.
Print Assumptions model_write_holds_talk.
