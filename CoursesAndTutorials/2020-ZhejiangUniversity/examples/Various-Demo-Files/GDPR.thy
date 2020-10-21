theory GDPR imports SDL          (* Christoph Benzmüller & Xavier Parent, 2018 *)

begin (*** GDPR Example ***)
 consts process_data_lawfully::\<sigma> erase_data::\<sigma> kill_boss::\<sigma>

 axiomatization where
  (* It is an obligation to process data lawfully. *)
    A1: "\<lfloor>\<^bold>O\<^bold>\<langle>process_data_lawfully\<^bold>\<rangle>\<rfloor>"  and
  (* Implicit: It is an obligation to keep the data if it was processed lawfully. *)
    Implicit: "\<lfloor>\<^bold>O\<^bold>\<langle>process_data_lawfully \<^bold>\<rightarrow> \<^bold>\<not>erase_data\<^bold>\<rangle>\<rfloor>" and
  (* If data was not processed lawfully, then it is an obligation to erase the data. *)
    A2: "\<lfloor>\<^bold>\<not>process_data_lawfully \<^bold>\<rightarrow> \<^bold>O\<^bold>\<langle>erase_data\<^bold>\<rangle>\<rfloor>" 
  (* Given a situation where data is processed unlawfully. *) and
    A3: "\<lfloor>\<^bold>\<not>process_data_lawfully\<rfloor>\<^sub>c\<^sub>w" 

 (*** Some Experiments ***) 
  lemma True  nitpick [satisfy] oops  (* Consistency-check: Is there a model? *) 
  lemma False sledgehammer      oops  (* Inconsistency-check: Can Falsum be derived? *) 

  lemma "\<lfloor>\<^bold>O\<^bold>\<langle>erase_data\<^bold>\<rangle>\<rfloor>"   sledgehammer nitpick oops  (* Should the data be erased? *)
  lemma "\<lfloor>\<^bold>O\<^bold>\<langle>\<^bold>\<not>erase_data\<^bold>\<rangle>\<rfloor>"  sledgehammer nitpick oops  (* Should the data be kept? *)
  lemma "\<lfloor>\<^bold>O\<^bold>\<langle>kill_boss\<^bold>\<rangle>\<rfloor>"    sledgehammer nitpick oops  (* Should the boss be killed? *)            
end




    
 