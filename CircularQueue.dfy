/*
    method adicionar(element: int)
    requires IsValid()
    modifies this
    //ensures filaAbstrata == old(filaAbstrata) + [element]
    ensures IsValid()
    {   
        var novoArray := new int[capacidade];
        if (tamanho == capacidade) {
            novoArray := new int[2 * capacidade];
        }
        var i := 0;
        while(i < tamanho) 
        invariant 0 <= i <= tamanho <= elementos.Length <= novoArray.Length; 
        {
            var index := inicio + i;

            novoArray[i] := elementos[index % elementos.Length];
            
            i := i + 1;
        }
        
        capacidade := 2 * capacidade;
        inicio := 0;
        fim := tamanho;
        
        
        novoArray[fim] := element;
        fim := (fim + 1) % elementos.Length;
        tamanho := tamanho + 1;
        filaAbstrata := filaAbstrata + [element];
        elementos := novoArray;
    }
    */



class CircularQueue{
    var tamanho: int;
    var inicio: int;
    var fim: int;
    var elementos: array<int>;
    //var filaAbstrata: seq<int>;

    predicate IsValid() reads this, elementos {
        0 <= inicio < elementos.Length &&
        0 <= fim < elementos.Length &&
        0 <= tamanho <= elementos.Length
        //tamanho == |filaAbstrata| 
        //(forall i: int :: 0 <= i < tamanho ==> elementos[(inicio + i) % elementos.Length] == filaAbstrata[i])
    }

    constructor (cap: int)
    requires cap > 0
    ensures IsValid() && tamanho == 0
    {
        var newElementos := new int[cap];
        tamanho := 0;
        inicio := 0;
        fim := 0;
        elementos := newElementos;
        //filaAbstrata := [];
    }


    method EstaVazia() returns (vazia: bool)
    requires IsValid()
    ensures vazia <==> tamanho == 0
    {
        vazia := tamanho == 0;
    }

    method Tamanho() returns (n: int)
        requires IsValid()
        ensures n == tamanho
    {
        n := tamanho;
    }

    method Contem(element: int) returns (contains: bool)
    requires IsValid()
    //ensures contains <==> (forall i: int ::  0 <= i < tamanho ==> elementos[i] == element)
    ensures IsValid()
    {
        var i := 0;

        while(i < tamanho)
        invariant 0 <= i <= tamanho; 
        {
            if(elementos[(inicio + i) % elementos.Length] == element){
                contains := true;
            }
            i := i + 1;
        }
        contains := false;
    }

    
    method adicionar(element: int)
    requires IsValid()
    modifies this
    ensures IsValid()
    {   
        

        var novoArray := new int[2 * elementos.Length];
        if (tamanho == elementos.Length) {
            
            var i := 0;
            while(i < tamanho) 
            invariant 0 <= i <= tamanho <= elementos.Length < novoArray.Length; 
            {
                var index := inicio + i;

                novoArray[i] := elementos[index % elementos.Length];
                
                i := i + 1;
            }
            elementos := novoArray;
            inicio := 0;
            fim := tamanho;
            novoArray[fim] := element;
            fim := (fim + 1) % elementos.Length;
           
            tamanho := tamanho + 1;
            //filaAbstrata := filaAbstrata + [element];
            elementos := novoArray;
        }else if(tamanho < elementos.Length){
            var novoArray_igual := new int[elementos.Length];
            var i := 0;
            while(i < tamanho) 
            invariant 0 <= i <= tamanho <= novoArray_igual.Length == elementos.Length; 
            {
                novoArray_igual[i] := elementos[i];
                i := i + 1;
            }
            if(fim < novoArray_igual.Length && fim > 0){
                novoArray_igual[fim] := element;
                fim := (fim + 1) % novoArray_igual.Length;
                if(tamanho < elementos.Length){
                    tamanho := tamanho + 1;
                }
                
                //filaAbstrata := filaAbstrata + [element];
            }
            elementos := novoArray_igual;
        }

    }
    

    

}

method main()
{
    var fila := new CircularQueue(5);
    var tamanho := fila.Tamanho();
    //var numero_elementos := fila.NumeroElementos();
    var vazia := fila.EstaVazia();

    assert tamanho == 0;
    //assert numero_elementos == 0;
    assert vazia == true;
    
    //fila.adicionar(1);
   
    
    var esta_vazia := fila.EstaVazia();
    
    assert esta_vazia;
}


/*
x Construtor deve instanciar uma fila vazia.
(testar) Adicionar um novo elemento na fila.
• Remover um elemento da fila e retornar seu valor caso a fila contenha elementos.
(testar) Verificar se um determinado elemento pertence o não a fila.
x Retornar o número de elementos da fila.
x Verificar se a fila é vazia ou não.
• Realizar a concatenação de duas filas, retornando uma nova fila como resultado, sem 
alterar as filas originais.
*/